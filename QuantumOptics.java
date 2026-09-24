import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.geom.Line2D;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

/**
 * QuantumOptics -- a 2D scalar Huygens-Fresnel wave-optics simulator with an interactive editor.
 *
 * ONE primitive: a Surface -- a flat segment with a complex refractive index on each side
 * (front / back): real part from the light SPEED (index n = 1/speed; a speed jump IS refraction)
 * and imaginary part `kappa` (absorption: 0 = dielectric, >0 = metal/lossy). A surface can also be
 * flagged `opaque` (a hard absorbing wall). How much light reflects vs. transmits comes from the
 * FRESNEL equations at the arrival angle -- not a hand-set coefficient -- so a ~4% glass
 * back-reflection, total internal reflection, and metallic mirrors all emerge.
 *
 * Every object compiles to surfaces:
 *    lens / prism / polygon = dielectric interfaces (glass on the inside)
 *    mirror = a metal (complex index); wall = opaque; a slit = walls with a gap
 *    a gap/aperture = a transmit-only (air|air) surface across the opening, discretized like any
 *                     surface; single- and double-slit diffraction EMERGE from the wavelet sum.
 *
 * ENGINE: each surface is discretized into omnidirectional point re-emitters (Huygens wavelets).
 * The source plane wave lights them (gen 0); then they light each other in coherent bounces, each
 * transfer split by Fresnel at its arrival angle. Every pixel sums the complex phasors reaching it;
 * |field|^2 per wavelength -> CIE 1931 XYZ -> sRGB. Refraction, focus, diffraction, dispersion, and
 * interference all fall out of the phasor sum.
 *
 *   javac QuantumOptics.java && java QuantumOptics
 *   java QuantumOptics --headless edit    (renders test-scene PNGs)
 */
public class QuantumOptics extends JPanel {

    static final int DEFW = 900, DEFH = 600;   // initial window size; the render then FOLLOWS the window (Scene.W/H)
    static final double SURF_SPACING = 4.0;   // re-emitter spacing along a surface (~half wavelength)
    static final double RENDER_STEP = 3.0;    // render-only: sub-sample each emitter's segment this finely
    static final double BASE_PX = 12.0;       // pixel wavelength at 550 nm (the reference scale)
    static final int ANG_BINS = 1024;         // directions in each emitter's angular visibility map
    static int groupCounter = 0;              // hands out unique group ids to optical faces
    static final double NYQ_FRAC = 0.5;      // emitter spacing = this * wavelength (oversample past Nyquist
                                              // to suppress the discrete-array spokes; 0.5 = bare Nyquist)
    static final double SOFT = 6.0;           // near-field softening for 1/sqrt(r)
    static final int FBINS = 129;             // Fresnel lookup resolution over cos(incidence) in [0,1]
    static final double GAMMA = 0.45, PCTILE = 0.995;
    static final double N_MIN = 0.3, N_MAX = 3.0;   // editable index range (n<1 allowed: metals, plasmas, diverging glass)

    // Dispersion spread across the visible band, added to each surface's OWN base index (1/speed).
    static final double DISPERSION = 0.06;
    static double effSpeed(Scene sc, double speed, double nm) {
        if (!sc.dispersive || speed >= 0.999) return speed;   // air (speed 1) never disperses
        double nBase = 1.0 / speed;                           // this surface's index
        double nEff  = nBase + DISPERSION * (550.0 - nm) / 140.0;  // blue (short nm) bends more
        return 1.0 / nEff;
    }

    // ------------------------------------------------------------- FAST TRIG
    static final int TAB = 1 << 14, MASK = TAB - 1;
    static final double[] SINT = new double[TAB];
    static { for (int i = 0; i < TAB; i++) SINT[i] = Math.sin(2 * Math.PI * i / TAB); }
    static final double TO_IDX = TAB / (2 * Math.PI);
    static double fastSin(double x) { return SINT[((int)(x * TO_IDX)) & MASK]; }
    static double fastCos(double x) { return SINT[((int)(x * TO_IDX) + (TAB >> 2)) & MASK]; }

    // recursive-branching controls
    static final int MAX_BOUNCES = 6;         // hard cap on generations (backstop)
    static final double BRANCH_THRESH = 1e-3; // drop the recursion once a bounce adds < this fraction of gen-0 energy

    // ============================================================================ SURFACE
    // The Surface primitive lives in Surface.java. The Fresnel table-building for it is below.

    // ---- Fresnel (complex indices, unpolarized, angle-dependent) --------------------------------
    // Build this surface's reflect/transmit coefficient tables at wavelength `lam`. Incident from the
    // front side sees medium(front) -> medium(back); from the back, the reverse. Each entry is the
    // complex amplitude the arriving field is multiplied by to get the reflected (same side) and
    // transmitted (far side) re-emission. Energy is split as power: |reflect|^2=R, |transmit|^2=1-R,
    // so it conserves by construction (the sqrt(k/2pi) re-emission already handles the impedance jump).
    static void buildFresnel(Scene sc, Surface s, double lam){
        if(s.opaque){ for(int b=0;b<FBINS;b++){ java.util.Arrays.fill(s.frF[b],0); java.util.Arrays.fill(s.frB[b],0); } return; }
        double nF = 1.0/effSpeed(sc, s.speedFront, lam), nB = 1.0/effSpeed(sc, s.speedBack, lam);
        for(int b=0;b<FBINS;b++){
            double c1 = b/(double)(FBINS-1);
            fresnelInto(nF, s.kappaFront, nB, s.kappaBack, c1, s.frF[b]);   // incident FROM front: n_i=front, n_t=back
            fresnelInto(nB, s.kappaBack, nF, s.kappaFront, c1, s.frB[b]);   // incident FROM back
        }
    }
    // reflect/transmit multipliers for incidence-cosine c1 at an interface n_i -> n_t (complex indices).
    static void fresnelInto(double niR,double niI,double ntR,double ntI,double c1,double[] out){
        double s1=Math.sqrt(Math.max(0,1-c1*c1));
        double den=ntR*ntR+ntI*ntI+1e-30;                                   // sinθ2 = (n_i/n_t) sinθ1
        double qR=(niR*ntR+niI*ntI)/den, qI=(niI*ntR-niR*ntI)/den;
        double s2R=qR*s1, s2I=qI*s1;
        double s2sqR=s2R*s2R-s2I*s2I, s2sqI=2*s2R*s2I;                       // cosθ2 = sqrt(1 - sin^2θ2)
        double[] c2=csqrt(1-s2sqR, -s2sqI); double c2R=c2[0], c2I=c2[1];
        if(c2I<0){ c2R=-c2R; c2I=-c2I; }                                     // decaying branch (evanescent past TIR)
        double Ac1R=niR*c1, Ac1I=niI*c1;                                     // n_i cosθ1
        double Bc2R=ntR*c2R-ntI*c2I, Bc2I=ntR*c2I+ntI*c2R;                   // n_t cosθ2
        double Bc1R=ntR*c1, Bc1I=ntI*c1;                                     // n_t cosθ1
        double Ac2R=niR*c2R-niI*c2I, Ac2I=niR*c2I+niI*c2R;                   // n_i cosθ2
        double[] rs=cdiv(Ac1R-Bc2R,Ac1I-Bc2I, Ac1R+Bc2R,Ac1I+Bc2I);         // s-pol reflect
        double[] rp=cdiv(Bc1R-Ac2R,Bc1I-Ac2I, Bc1R+Ac2R,Bc1I+Ac2I);         // p-pol reflect
        double[] ts=cdiv(2*Ac1R,2*Ac1I, Ac1R+Bc2R,Ac1I+Bc2I);              // s-pol transmit (for phase)
        double[] tp=cdiv(2*Ac1R,2*Ac1I, Bc1R+Ac2R,Bc1I+Ac2I);              // p-pol transmit
        double Rs=rs[0]*rs[0]+rs[1]*rs[1], Rp=rp[0]*rp[0]+rp[1]*rp[1];
        double R=0.5*(Rs+Rp); if(R>1) R=1; double T=1-R;                     // unpolarized average
        double rPh=Math.atan2(0.5*(rs[1]+rp[1]), 0.5*(rs[0]+rp[0]));         // blended phase
        double tPh=Math.atan2(0.5*(ts[1]+tp[1]), 0.5*(ts[0]+tp[0]));
        double rMag=Math.sqrt(R), tMag=Math.sqrt(Math.max(0,T));
        out[0]=rMag*Math.cos(rPh); out[1]=rMag*Math.sin(rPh);
        out[2]=tMag*Math.cos(tPh); out[3]=tMag*Math.sin(tPh);
    }
    static double[] csqrt(double aR,double aI){ double m=Math.hypot(aR,aI);
        double re=Math.sqrt(Math.max(0,(m+aR)/2)), im=Math.sqrt(Math.max(0,(m-aR)/2));
        return new double[]{re, aI<0?-im:im};
    }
    static double[] cdiv(double aR,double aI,double bR,double bI){ double d=bR*bR+bI*bI+1e-30;
        return new double[]{(aR*bR+aI*bI)/d, (aI*bR-aR*bI)/d};
    }

    // ---- occlusion: does open segment (ax,ay)-(bx,by) cross any surface (excluding e1,e2)? ----
    static boolean segCross(double ax,double ay,double bx,double by,double cx,double cy,double dx,double dy){
        double rx=bx-ax, ry=by-ay, sx=dx-cx, sy=dy-cy;
        double den=rx*sy-ry*sx; if(Math.abs(den)<1e-9) return false;
        double t=((cx-ax)*sy-(cy-ay)*sx)/den, u=((cx-ax)*ry-(cy-ay)*rx)/den;
        // u (along the blocking surface) is INCLUSIVE of endpoints, so a ray through a shared vertex
        // between two adjacent facets is caught (otherwise the source leaks a line through the crack).
        return t>1e-4 && t<1-1e-4 && u>=-1e-4 && u<=1+1e-4;
    }
    // rasterize surface s into emitter P's angular depth buffer: for each direction bin the surface
    // spans, store the distance from P to the segment (varies across the span between its two vertices).
    static void rasterDepth(double px,double py, Surface s, double[] d, int NB){
        double ax=s.x1-px, ay=s.y1-py, bx=s.x2-px, by=s.y2-py;
        double th1=Math.atan2(ay,ax), th2=Math.atan2(by,bx);
        double diff=th2-th1; while(diff<=-Math.PI) diff+=2*Math.PI; while(diff>Math.PI) diff-=2*Math.PI;   // shorter arc
        int steps=Math.max(1,(int)(Math.abs(diff)*NB/(2*Math.PI))+1);
        double ABx=s.x2-s.x1, ABy=s.y2-s.y1, sc2=NB/(2*Math.PI);
        for(int i=0;i<=steps;i++){
            double th=th1+diff*i/steps, dx=Math.cos(th), dy=Math.sin(th);
            double det=ABx*dy-ABy*dx; if(Math.abs(det)<1e-9) continue;
            double t=(-ax*ABy + ABx*ay)/det, u=(dx*ay - dy*ax)/det;   // ray P+t*dir hits segment at param u
            if(t>0 && u>=-0.01 && u<=1.01){
                int bin=((int)((th+Math.PI)*sc2)) & (NB-1);
                if(t<d[bin]) d[bin]=t;
            }
        }
    }

    // DDA over the grid: visit only the cells the ray crosses, tight int loop
    static boolean occluded(Scene sc,double ax,double ay,double bx,double by,Surface e1,Surface e2){
        final double G=Scene.GCELL; final int gc=sc.gCols, gr=sc.gRows;
        final Surface[] SA=sc.surfArr; final int[][] CS=sc.cellSurf;
        final int g1=(e1!=null&&e1.group>=0)?e1.group:Integer.MIN_VALUE;   // a face's co-facets never self-shadow it
        final int g2=(e2!=null&&e2.group>=0)?e2.group:Integer.MIN_VALUE;
        if(SA.length < 48){   // few surfaces -> a plain bbox loop beats grid traversal
            double minx=Math.min(ax,bx),maxx=Math.max(ax,bx),miny=Math.min(ay,by),maxy=Math.max(ay,by);
            for(Surface s: SA){ if(s==e1||s==e2||s.group==g1||s.group==g2) continue;
                if(Math.max(s.x1,s.x2)<minx||Math.min(s.x1,s.x2)>maxx||Math.max(s.y1,s.y2)<miny||Math.min(s.y1,s.y2)>maxy) continue;
                if(segCross(ax,ay,bx,by,s.x1,s.y1,s.x2,s.y2)) return true; }
            return false;
        }
        double dx=bx-ax, dy=by-ay;
        int cx=(int)(ax/G), cy=(int)(ay/G), cxe=(int)(bx/G), cye=(int)(by/G);
        int stepX = dx>0?1:(dx<0?-1:0), stepY = dy>0?1:(dy<0?-1:0);
        double tDX = dx!=0? Math.abs(G/dx):1e30, tDY = dy!=0? Math.abs(G/dy):1e30;
        double tMX = dx!=0? ((stepX>0?(cx+1)*G:cx*G)-ax)/dx : 1e30;
        double tMY = dy!=0? ((stepY>0?(cy+1)*G:cy*G)-ay)/dy : 1e30;
        for(int guard=0; guard<gc+gr+4; guard++){
            if(cx>=0&&cy>=0&&cx<gc&&cy<gr){
                int[] list=CS[cy*gc+cx];
                for(int k=0;k<list.length;k++){ Surface s=SA[list[k]];
                    if(s==e1||s==e2||s.group==g1||s.group==g2) continue;
                    if(segCross(ax,ay,bx,by, s.x1,s.y1,s.x2,s.y2)) return true; }
            }
            if(cx==cxe && cy==cye) break;
            if(tMX<tMY){ cx+=stepX; tMX+=tDX; } else { cy+=stepY; tMY+=tDY; }
        }
        return false;
    }

    // ============================================================================ SCENE
    static final class Scene {
        String name;
        int W = DEFW, H = DEFH;      // render dimensions = the window size at simulate time (fixed for this scene's life)
        double[] wlNm;               // wavelengths (nm)
        double basePx;               // px wavelength at 550 nm
        // SOURCE: a line segment; the beam travels perpendicular to it (the only directional emitter).
        double sax,say,sbx,sby;      // source line endpoints
        double sdx,sdy;              // unit beam direction (perpendicular to the line)
        double stx,sty, slen;        // unit line tangent, source width
        List<Surface> surfaces = new ArrayList<>();
        boolean dispersive = false;
        double gamma = GAMMA, pctile = PCTILE;
        double exposure = 18.0;          // FIXED tone-map divisor (source luminance = 1); scene-independent
        RenderData rdata;                // cached raw XYZ field (for instant re-exposure without recompute)
        double segLen = SURF_SPACING;   // re-emitter spacing for ALL surfaces (driven by the segment slider)
        int maxBounces = MAX_BOUNCES;   // recursion hard cap (configurable)

        void setSource(double ax,double ay,double bx,double by){
            sax=ax;say=ay;sbx=bx;sby=by;
            double dx=bx-ax, dy=by-ay; slen=Math.hypot(dx,dy)+1e-9;
            stx=dx/slen; sty=dy/slen; sdx=sty; sdy=-stx;   // beam = tangent rotated -90 deg
        }
        // forward distance of P from the source plane (>=0 downstream), and whether P is within the beam column
        double srcForward(double px,double py){ return (px-sax)*sdx + (py-say)*sdy; }
        boolean inBeam(double px,double py){
            double along=(px-sax)*stx + (py-say)*sty;
            return along>=0 && along<=slen && srcForward(px,py)>=-1e-6;
        }
        double lambdaPx(int w) { return basePx * (wlNm[w] / 550.0); }
        double lambdaMaxPx()   { double m=0; for (double nm: wlNm) m=Math.max(m, basePx*nm/550.0); return m; }
        double lambdaMinPx()   { double m=1e9; for (double nm: wlNm) m=Math.min(m, basePx*nm/550.0); return m; }

        // spatial grid (int CSR) so occlusion only tests surfaces near a ray
        static final double GCELL = 32;
        int gCols, gRows; Surface[] surfArr; int[][] cellSurf;
        void buildGrid(){
            surfArr = surfaces.toArray(new Surface[0]);
            gCols=(int)Math.ceil(W/GCELL); gRows=(int)Math.ceil(H/GCELL); int nc=gCols*gRows;
            int[] cnt=new int[nc];
            for(Surface s: surfArr){ int c0=cl((int)(Math.min(s.x1,s.x2)/GCELL),gCols),c1=cl((int)(Math.max(s.x1,s.x2)/GCELL),gCols);
                int r0=cl((int)(Math.min(s.y1,s.y2)/GCELL),gRows),r1=cl((int)(Math.max(s.y1,s.y2)/GCELL),gRows);
                for(int r=r0;r<=r1;r++)for(int c=c0;c<=c1;c++) cnt[r*gCols+c]++; }
            cellSurf=new int[nc][]; for(int c=0;c<nc;c++) cellSurf[c]=new int[cnt[c]];
            int[] fill=new int[nc];
            for(int si=0;si<surfArr.length;si++){ Surface s=surfArr[si];
                int c0=cl((int)(Math.min(s.x1,s.x2)/GCELL),gCols),c1=cl((int)(Math.max(s.x1,s.x2)/GCELL),gCols);
                int r0=cl((int)(Math.min(s.y1,s.y2)/GCELL),gRows),r1=cl((int)(Math.max(s.y1,s.y2)/GCELL),gRows);
                for(int r=r0;r<=r1;r++)for(int c=c0;c<=c1;c++){ int ci=r*gCols+c; cellSurf[ci][fill[ci]++]=si; } }
        }
        static int cl(int v,int n){ return v<0?0:(v>=n?n-1:v); }

        void build() { double lmin=lambdaMinPx(); for (Surface s : surfaces) s.discretize(lmin, segLen); buildGrid(); }
    }

    // ============================================================================ PROPAGATION
    // Recursive branching (no left->right assumption): the source illuminates every surface it can
    // reach unoccluded; each surface re-emits omnidirectionally (front+back) via its type; that light
    // reaches every other unoccluded surface; repeat as generations (bounces), coherently summing,
    // until a bounce adds negligible energy or MAX_BOUNCES is hit.
    static void propagate(Scene sc) {
        int nw = sc.wlNm.length;
        java.util.List<Surface> S = sc.surfaces;
        for (Surface s : S) s.alloc(nw);

        for (int w = 0; w < nw; w++) {
            double k0 = 2 * Math.PI / sc.lambdaPx(w), lam = sc.wlNm[w];

            // ---- generation 0: the source ----
            for (Surface s : S) buildFresnel(sc, s, lam);   // per-wavelength reflect/transmit tables
            double e0 = 0;
            for (Surface s : S) for (int e = 0; e < s.n; e++) {
                double oFr=0,oFi=0,oBr=0,oBi=0;
                if (!s.opaque && sc.inBeam(s.ex[e],s.ey[e])) {
                    double Px=s.ex[e], Py=s.ey[e], f = sc.srcForward(Px,Py);
                    if (!occluded(sc, Px-f*sc.sdx, Py-f*sc.sdy, Px, Py, s, null)) {
                        double ph = k0*f, cr=fastCos(ph), ci=fastSin(ph);
                        double cosN = s.nx[e]*sc.sdx + s.ny[e]*sc.sdy;   // beam vs normal
                        int bin=(int)(Math.abs(cosN)*(FBINS-1)+0.5);
                        double[] fr = (cosN<0)? s.frF[bin] : s.frB[bin];  // <0: beam hits front side
                        double rr=fr[0],ri=fr[1], tr=fr[2],ti=fr[3];
                        double rRe=rr*cr-ri*ci, rIm=rr*ci+ri*cr;          // reflected (arrival side)
                        double tRe=tr*cr-ti*ci, tIm=tr*ci+ti*cr;          // transmitted (far side)
                        if (cosN<0){ oFr=rRe; oFi=rIm; oBr=tRe; oBi=tIm; } // arrive front: reflect->front, transmit->back
                        else       { oBr=rRe; oBi=rIm; oFr=tRe; oFi=tIm; } // arrive back
                    }
                }
                s.pFr[w][e]=oFr; s.pFi[w][e]=oFi; s.pBr[w][e]=oBr; s.pBi[w][e]=oBi;
                s.tFr[w][e]+=oFr; s.tFi[w][e]+=oFi; s.tBr[w][e]+=oBr; s.tBi[w][e]+=oBi;
                e0 = Math.max(e0, oFr*oFr+oFi*oFi+oBr*oBr+oBi*oBi);   // PEAK element intensity
            }
            double thresh = BRANCH_THRESH*e0 + 1e-30;

            // ---- bounces ----
            for (int gen=1; gen<=sc.maxBounces; gen++) {
                for (Surface s : S) for (int e=0;e<s.n;e++){ s.iFr[w][e]=s.iFi[w][e]=s.iBr[w][e]=s.iBi[w][e]=0; }
                for (Surface se : S) for (int e=0; e<se.n; e++) {
                    if (se.opaque) continue;                            // a wall absorbs -> emits nothing
                    double Pex=se.ex[e], Pey=se.ey[e], nex=se.nx[e], ney=se.ny[e];
                    double oFr=0,oFi=0,oBr=0,oBi=0;                     // OUTGOING per side (Fresnel applied at arrival)
                    for (Surface sj : S) { if (sj==se) continue;
                        for (int j=0;j<sj.n;j++) {
                            double Pjx=sj.ex[j], Pjy=sj.ey[j];
                            double dxj=Pex-Pjx, dyj=Pey-Pjy;
                            double emitDot = dxj*sj.nx[j] + dyj*sj.ny[j];   // >0: e is on j's front side
                            for (int side=0; side<2; side++) {
                                double pr,pi,speed,kap;
                                if (side==0){ if(emitDot<=0) continue; pr=sj.pFr[w][j]; pi=sj.pFi[w][j]; speed=sj.speedFront; kap=sj.kappaFront; }
                                else        { if(emitDot>=0) continue; pr=sj.pBr[w][j]; pi=sj.pBi[w][j]; speed=sj.speedBack;  kap=sj.kappaBack; }
                                if (pr==0 && pi==0) continue;
                                if (occluded(sc, Pjx,Pjy, Pex,Pey, sj, se)) continue;   // ALL surfaces shadow (match render): a downstream surface sees only the exit facet, not front+back (double count)
                                double r = Math.hypot(dxj,dyj)+1e-9;
                                double k = k0/effSpeed(sc, speed, lam);
                                double obl = Math.abs(emitDot)/r;   // Huygens obliquity (cos of emission angle from normal)
                                // sqrt(k/2pi): 2D free-space normalization (energy + colour). exp(-k0*kappa*r): absorption over the path through this medium.
                                double inv = sj.wgt[j]/Math.sqrt(r+SOFT) * obl * Math.sqrt(k/(2*Math.PI));
                                if (kap>0) inv *= Math.exp(-k0*kap*r);
                                double ph = k*r, c=fastCos(ph), sn=fastSin(ph);
                                double cr=(pr*c-pi*sn)*inv, ci=(pr*sn+pi*c)*inv;    // field arriving at e
                                // apply se's Fresnel at the arrival angle: reflect -> arrival side, transmit -> far side
                                int bin=(int)(Math.abs(dxj*nex+dyj*ney)/r*(FBINS-1)+0.5);
                                boolean front = (Pjx-Pex)*nex + (Pjy-Pey)*ney > 0;   // j on e's front side
                                double[] fr = front? se.frF[bin] : se.frB[bin];
                                double rRe=fr[0]*cr-fr[1]*ci, rIm=fr[0]*ci+fr[1]*cr;
                                double tRe=fr[2]*cr-fr[3]*ci, tIm=fr[2]*ci+fr[3]*cr;
                                if (front){ oFr+=rRe; oFi+=rIm; oBr+=tRe; oBi+=tIm; }
                                else      { oBr+=rRe; oBi+=rIm; oFr+=tRe; oFi+=tIm; }
                            }
                        }
                    }
                    se.iFr[w][e]=oFr; se.iFi[w][e]=oFi; se.iBr[w][e]=oBr; se.iBi[w][e]=oBi;
                }
                double ge = 0;
                for (Surface s : S) for (int e=0;e<s.n;e++) {           // accumulators already hold outgoing (Fresnel applied)
                    double o0=s.iFr[w][e],o1=s.iFi[w][e],o2=s.iBr[w][e],o3=s.iBi[w][e];
                    s.pFr[w][e]=o0; s.pFi[w][e]=o1; s.pBr[w][e]=o2; s.pBi[w][e]=o3;
                    s.tFr[w][e]+=o0; s.tFi[w][e]+=o1; s.tBr[w][e]+=o2; s.tBi[w][e]+=o3;
                    ge = Math.max(ge, o0*o0+o1*o1+o2*o2+o3*o3);   // PEAK, not summed energy
                }
                if (ge < thresh) break;   // drop when the brightest new emission is negligible
            }
        }
    }

    // ============================================================================ RENDER
    static BufferedImage render(Scene sc) {
        final int W = sc.W, H = sc.H;                 // render at the window's current size
        int nw = sc.wlNm.length;
        // CIE 1931 color-matching weights per wavelength; a spectrum composites in XYZ then -> sRGB
        double[][] cmf = new double[nw][];
        for (int w = 0; w < nw; w++) cmf[w] = cieXYZ(sc.wlNm[w]);

        final float[] accX = new float[W*H], accY = new float[W*H], accZ = new float[W*H];

        final java.util.List<Surface> S = sc.surfaces;
        // source shadow is wavelength-independent -> precompute once (clear? + forward distance)
        final boolean[] sclear = new boolean[W*H]; final float[] sfwd = new float[W*H];
        IntStream.range(0, H).parallel().forEach(py -> { for (int px=0; px<W; px++) {
            if (sc.inBeam(px,py)) { double f=sc.srcForward(px,py);
                if (!occluded(sc, px-f*sc.sdx, py-f*sc.sdy, px, py, null, null)) { sclear[py*W+px]=true; sfwd[py*W+px]=(float)f; } }
        }});

        final double[] k0a = new double[nw], lamA = new double[nw];
        for(int w=0;w<nw;w++){ k0a[w]=2*Math.PI/sc.lambdaPx(w); lamA[w]=sc.lambdaPx(w); }

        // collect only ACTIVE emitters (nonzero amplitude) -> absorbers/dead elements are skipped entirely
        java.util.List<Surface> aS=new ArrayList<>(); java.util.List<Integer> aE=new ArrayList<>();
        for(Surface s:S){
            for(int e=0;e<s.n;e++){ boolean act=false;
                for(int w=0;w<nw&&!act;w++) if(s.tFr[w][e]!=0||s.tFi[w][e]!=0||s.tBr[w][e]!=0||s.tBi[w][e]!=0) act=true;
                if(act){ aS.add(s); aE.add(e); } }
        }
        final Surface[] AS=aS.toArray(new Surface[0]); final int[] AE=new int[aE.size()];
        for(int i=0;i<AE.length;i++) AE[i]=aE.get(i);

        // ANGULAR VISIBILITY: precompute, once per emitter, the nearest-surface distance in each of
        // ANG_BINS directions around it (its own surface excluded). Then "is emitter->pixel blocked?"
        // is an O(1) lookup: is the nearest surface in that direction closer than the pixel?
        final int NB = ANG_BINS; final double binScale = NB/(2*Math.PI);
        final double[][] depth = new double[AS.length][];
        IntStream.range(0, AS.length).parallel().forEach(ai -> {
            Surface own=AS[ai]; int e=AE[ai]; double px0=own.ex[e], py0=own.ey[e];
            double[] d=new double[NB]; java.util.Arrays.fill(d, Double.POSITIVE_INFINITY);
            for(Surface s: S){ if(s==own || (own.group>=0 && s.group==own.group)) continue;   // don't self-shadow a face
                rasterDepth(px0,py0,s,d,NB); }
            depth[ai]=d;
        });

        // occlusion is wavelength-independent, so it is tested ONCE per pixel-emitter; wavelengths are inner.
        IntStream.range(0, H).parallel().forEach(py -> {
            double[] re = new double[nw], im = new double[nw];
            for (int px = 0; px < W; px++) {
                int idx = py*W+px;
                java.util.Arrays.fill(re,0); java.util.Arrays.fill(im,0);
                if (sclear[idx]) { double f=sfwd[idx]; for(int w=0;w<nw;w++){ double ph=k0a[w]*f; re[w]+=fastCos(ph); im[w]+=fastSin(ph);} }
                for (int ai=0; ai<AS.length; ai++) {
                    Surface s=AS[ai]; int e=AE[ai];
                    double cdx = px-s.ex[e], cdy = py-s.ey[e];
                    boolean front = cdx*s.nx[e] + cdy*s.ny[e] > 0;
                    double speed = front ? s.speedFront : s.speedBack;
                    double r0 = Math.sqrt(cdx*cdx+cdy*cdy)+1e-9;      // angular-map occlusion lookup
                    int bin = ((int)((Math.atan2(cdy,cdx)+Math.PI)*binScale)) & (NB-1);
                    if (depth[ai][bin] < r0-0.75) continue;          // a surface is between emitter and pixel
                    // render the element as an EVEN line-source over its surface span (not a point):
                    double fLen = Math.hypot(s.x2-s.x1, s.y2-s.y1) + 1e-9;
                    int K = Math.max(1, (int)Math.round((fLen/s.n)/RENDER_STEP));
                    double wk = s.wgt[e]/K;
                    for (int kk=0; kk<K; kk++) {
                        double t=(e+(kk+0.5)/K)/(double)s.n;
                        double psx=s.x1+t*(s.x2-s.x1), psy=s.y1+t*(s.y2-s.y1);
                        double dxs=px-psx, dys=py-psy, rs=Math.sqrt(dxs*dxs+dys*dys)+1e-9;
                        double invs = wk/Math.sqrt(rs+SOFT) * (Math.abs(dxs*s.nx[e]+dys*s.ny[e])/rs);
                        for (int w=0; w<nw; w++) {
                            double a_r = front ? s.tFr[w][e] : s.tBr[w][e];
                            double a_i = front ? s.tFi[w][e] : s.tBi[w][e];
                            if (a_r==0 && a_i==0) continue;
                            double k = k0a[w]/effSpeed(sc, speed, sc.wlNm[w]);
                            double ph = k*rs, c=fastCos(ph), sn=fastSin(ph);
                            double g = invs*Math.sqrt(k/(2*Math.PI));   // Fresnel normalization
                            re[w] += (a_r*c - a_i*sn)*g;
                            im[w] += (a_r*sn + a_i*c)*g;
                        }
                    }
                }
                double X=0,Y=0,Z=0;
                for (int w=0; w<nw; w++){ double iv=re[w]*re[w]+im[w]*im[w];
                    X+=iv*cmf[w][0]; Y+=iv*cmf[w][1]; Z+=iv*cmf[w][2]; }
                accX[idx]=(float)X; accY[idx]=(float)Y; accZ[idx]=(float)Z;
            }
        });

        // WHITE BALANCE: the sampled wavelengths' equal-energy white point (sum of CMFs) must map to
        // sRGB's D65 white, or "white light" comes out tinted and the spectrum looks CMY. Scale so it does.
        double Xw=0,Yw=0,Zw=0; for(int w=0;w<nw;w++){ Xw+=cmf[w][0]; Yw+=cmf[w][1]; Zw+=cmf[w][2]; }
        double sx=0.95047/(Xw+1e-9), sy=1.0/(Yw+1e-9), sz=1.08883/(Zw+1e-9);
        // cache the raw XYZ field so brightness can be re-toned WITHOUT recomputing the simulation
        sc.rdata = new RenderData(accX, accY, accZ, sx, sy, sz);
        return toneMap(sc);
    }

    // cached raw field (XYZ + white balance) from the last render, so exposure changes are instant
    static final class RenderData { float[] X,Y,Z; double sx,sy,sz;
        RenderData(float[] x,float[] y,float[] z,double a,double b,double c){ X=x;Y=y;Z=z;sx=a;sy=b;sz=c; } }

    // CHEAP: apply exposure + tone curve to the cached XYZ (no field computation)
    // complex field at a pixel for one wavelength (same math as render) -- for energy/flux diagnostics
    static double[] fieldAt(Scene sc, double px, double py, int w){
        double k0=2*Math.PI/sc.lambdaPx(w), re=0, im=0;
        if(sc.inBeam(px,py)){ double f=sc.srcForward(px,py);
            if(!occluded(sc, px-f*sc.sdx, py-f*sc.sdy, px,py, null,null)){ double ph=k0*f; re+=Math.cos(ph); im+=Math.sin(ph); } }
        for(Surface s: sc.surfaces){ for(int e=0;e<s.n;e++){
            double cdx=px-s.ex[e], cdy=py-s.ey[e]; boolean front=cdx*s.nx[e]+cdy*s.ny[e]>0;
            double ar=front?s.tFr[w][e]:s.tBr[w][e], ai=front?s.tFi[w][e]:s.tBi[w][e];
            if(ar==0&&ai==0) continue;
            if(occluded(sc, s.ex[e],s.ey[e], px,py, s, null)) continue;
            double speed=front?s.speedFront:s.speedBack, k=k0/effSpeed(sc,speed,sc.wlNm[w]);
            double fLen=Math.hypot(s.x2-s.x1,s.y2-s.y1)+1e-9; int K=Math.max(1,(int)Math.round((fLen/s.n)/RENDER_STEP)); double wk=s.wgt[e]/K;
            for(int kk=0;kk<K;kk++){ double t=(e+(kk+0.5)/K)/(double)s.n, psx=s.x1+t*(s.x2-s.x1), psy=s.y1+t*(s.y2-s.y1);
                double dxs=px-psx, dys=py-psy, rs=Math.hypot(dxs,dys)+1e-9;
                double invs=wk/Math.sqrt(rs+SOFT)*(Math.abs(dxs*s.nx[e]+dys*s.ny[e])/rs)*Math.sqrt(k/(2*Math.PI)), ph=k*rs, c=Math.cos(ph), sn=Math.sin(ph);
                re+=(ar*c-ai*sn)*invs; im+=(ar*sn+ai*c)*invs; }
        }}
        return new double[]{re,im};
    }

    static BufferedImage toneMap(Scene sc){
        final int W = sc.W, H = sc.H;
        RenderData rd = sc.rdata;
        BufferedImage img = new BufferedImage(W, H, BufferedImage.TYPE_INT_RGB);
        double norm = sc.exposure;   // FIXED, scene-independent (source luminance = 1)
        for (int i=0;i<W*H;i++){
            double Xn=rd.X[i]*rd.sx/norm, Yn=rd.Y[i]*rd.sy/norm, Zn=rd.Z[i]*rd.sz/norm;
            double lr =  3.2406*Xn -1.5372*Yn -0.4986*Zn;
            double lg = -0.9689*Xn +1.8758*Yn +0.0415*Zn;
            double lb =  0.0557*Xn -0.2040*Yn +1.0570*Zn;
            int r=cieTone(lr,sc.gamma), gg=cieTone(lg,sc.gamma), b=cieTone(lb,sc.gamma);
            img.setRGB(i%W, i/W, (r<<16)|(gg<<8)|b);
        }
        Graphics2D g = img.createGraphics();
        drawOverlays(g, sc);
        g.dispose();
        return img;
    }

    // ============================================================================ OVERLAYS
    static void drawOverlays(Graphics2D g, Scene sc) {
        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        for (Surface s : sc.surfaces) {
            if (s.opaque) { g.setColor(new Color(70,70,80,200)); g.setStroke(new BasicStroke(4)); }                   // absorbing wall
            else if (Math.max(s.kappaFront,s.kappaBack) > 0.3) { g.setColor(new Color(120,230,255,220)); g.setStroke(new BasicStroke(3)); }  // metal / mirror
            else if (Math.abs(s.speedFront - s.speedBack) > 1e-6) { g.setColor(new Color(150,200,255,180)); g.setStroke(new BasicStroke(1.5f)); }  // refracting interface
            else continue;                                                                                            // air|air transmit (aperture) -> invisible
            g.draw(new java.awt.geom.Line2D.Double(s.x1, s.y1, s.x2, s.y2));
        }
        // source line + beam-direction arrow
        g.setColor(Color.WHITE); g.setStroke(new BasicStroke(3));
        g.draw(new java.awt.geom.Line2D.Double(sc.sax, sc.say, sc.sbx, sc.sby));
        double mx=(sc.sax+sc.sbx)/2, my=(sc.say+sc.sby)/2;
        g.setStroke(new BasicStroke(1));
        g.draw(new java.awt.geom.Line2D.Double(mx, my, mx+18*sc.sdx, my+18*sc.sdy));
    }

    // ============================================================================ COLOR (CIE 1931)
    // analytic CIE 1931 color-matching functions (Wyman, Sloan, Shirley 2013 multi-gaussian fit)
    static double cieG(double x,double mu,double s1,double s2){ double t=(x-mu)/(x<mu?s1:s2); return Math.exp(-0.5*t*t); }
    static double[] cieXYZ(double nm){
        double x = 1.056*cieG(nm,599.8,37.9,31.0) + 0.362*cieG(nm,442.0,16.0,26.7) - 0.065*cieG(nm,501.1,20.4,26.2);
        double y = 0.821*cieG(nm,568.8,46.9,40.5) + 0.286*cieG(nm,530.9,16.3,31.1);
        double z = 1.217*cieG(nm,437.0,11.8,36.0) + 0.681*cieG(nm,459.0,26.0,13.8);
        return new double[]{x,y,z};
    }
    static int cieTone(double lin, double gamma){
        lin = Math.max(0, lin);
        lin = lin/(1+lin);                              // Reinhard: soft highlight rolloff (no blowout, scene-independent)
        return (int)Math.max(0, Math.min(255, Math.round(255*Math.pow(lin, gamma))));
    }


    // ============================================================================ EDITOR
    static final double AIR = 1.0;                // ambient medium speed for created objects

    // ---- editable objects. Every object compiles down to flat Surfaces (+ the source). ----
    static final class Group { java.util.List<Surface> surfs = new ArrayList<>(); boolean occluder; double repX;
        Group(boolean occ){ occluder = occ; } }

    static abstract class EdObj {
        abstract double[][] handles();
        abstract void dragHandle(int i, double x, double y);
        abstract void moveBy(double dx, double dy);
        abstract boolean hit(double x, double y);
        abstract void draw(Graphics2D g, boolean sel, double seg);
        void build(java.util.List<Group> groups, java.util.List<Surface> loose, double seg) {}
    }

    static final class EdLight extends EdObj {
        double x1,y1,x2,y2;
        EdLight(double x1,double y1,double x2,double y2){ this.x1=x1;this.y1=y1;this.x2=x2;this.y2=y2; }
        double[][] handles(){ return new double[][]{{x1,y1},{x2,y2}}; }
        void dragHandle(int i,double x,double y){ if(i==0){x1=x;y1=y;} else {x2=x;y2=y;} }
        void moveBy(double dx,double dy){ x1+=dx;y1+=dy;x2+=dx;y2+=dy; }
        boolean hit(double x,double y){ return distSeg(x,y,x1,y1,x2,y2)<8; }
        void draw(Graphics2D g,boolean sel,double seg){
            g.setColor(new Color(255,235,120)); g.setStroke(new BasicStroke(3));
            g.draw(new Line2D.Double(x1,y1,x2,y2));
            double len=Math.hypot(x2-x1,y2-y1)+1e-9, tx=(x2-x1)/len, ty=(y2-y1)/len;
            double dx=ty, dy=-tx;                                     // beam direction (perpendicular to the line)
            g.setStroke(new BasicStroke(1));
            for(double f=0.2; f<=0.8001; f+=0.3){
                double bx=x1+(x2-x1)*f, by=y1+(y2-y1)*f, ex=bx+22*dx, ey=by+22*dy;
                g.draw(new Line2D.Double(bx,by,ex,ey));
                g.draw(new Line2D.Double(ex,ey, ex-6*dx+4*dy, ey-6*dy-4*dx));
                g.draw(new Line2D.Double(ex,ey, ex-6*dx-4*dy, ey-6*dy+4*dx));
            }
            drawHandles(g,this,sel);
        }
    }

    static final class EdLens extends EdObj {
        double cx,cy,h,t, n=1.6;
        EdLens(double cx,double cy,double h,double t){ this.cx=cx;this.cy=cy;this.h=h;this.t=t; }
        static final double CTHK = 12;   // center thickness of a concave lens
        // the two faces as x(dy). t>0 biconvex (fat middle, tips meet); t<0 biconcave (thin middle, thick edges)
        double frontX(double dy){ double u=dy/h; return t>=0 ? cx-(t/2)*(1-u*u) : cx-CTHK/2-(-t/2)*u*u; }
        double backX (double dy){ double u=dy/h; return t>=0 ? cx+(t/2)*(1-u*u) : cx+CTHK/2+(-t/2)*u*u; }
        double[][] handles(){ return new double[][]{{cx,cy-h},{cx,cy+h},{cx-t/2,cy}}; }
        void dragHandle(int i,double x,double y){
            if(i==0){ double botY=cy+h; cy=(y+botY)/2; h=Math.max(12,(botY-y)/2); cx=x; }
            else if(i==1){ double topY=cy-h; cy=(topY+y)/2; h=Math.max(12,(y-topY)/2); cx=x; }
            else { t=2*(cx-x); if(Math.abs(t)<2) t=(t<0?-2:2); }   // negative t -> concave (diverging) lens
        }
        void moveBy(double dx,double dy){ cx+=dx; cy+=dy; }
        boolean hit(double x,double y){ double dy=y-cy; return Math.abs(dy)<=h && x>=frontX(dy)-3 && x<=backX(dy)+3; }
        void draw(Graphics2D g,boolean sel,double seg){
            g.setColor(new Color(150,200,255,200)); g.setStroke(new BasicStroke(1.6f));
            int FAC=Math.max(2,(int)Math.ceil(2*h/seg));   // draw the ACTUAL facets used by the sim
            arc(g,false,FAC); arc(g,true,FAC);
            drawHandles(g,this,sel);
            g.setColor(new Color(180,210,255)); g.drawString(String.format("n=%.2f", n), (int)(cx-14), (int)(cy-h-8));
        }
        void arc(Graphics2D g,boolean back,int FAC){
            double px=back?backX(-h):frontX(-h), py=cy-h;
            for(int i=1;i<=FAC;i++){ double dy=-h+2*h*i/FAC; double x=back?backX(dy):frontX(dy), yy=cy+dy;
                g.draw(new Line2D.Double(px,py,x,yy)); px=x; py=yy; }
        }
        void build(java.util.List<Group> groups, java.util.List<Surface> loose, double seg){
            double glass=1.0/n;
            int FAC=Math.max(2,(int)Math.ceil(2*h/seg));   // facet the curve at the segment length
            double[] fx=new double[FAC+1],fy=new double[FAC+1],bx=new double[FAC+1],by=new double[FAC+1];
            for(int i=0;i<=FAC;i++){ double dy=-h+2*h*i/FAC;
                fx[i]=frontX(dy); fy[i]=cy+dy; bx[i]=backX(dy); by[i]=cy+dy; }
            Group front=new Group(false), back=new Group(false);
            int gf=++groupCounter, gb=++groupCounter;   // the two faces are separate optical surfaces
            for(int i=0;i<FAC;i++){
                front.surfs.add(glassFacet(fx[i],fy[i],fx[i+1],fy[i+1], glass, gf));  // glass is toward the lens center (cx,cy)
                back.surfs.add(glassFacet(bx[i],by[i],bx[i+1],by[i+1], glass, gb));   // works for convex AND concave
            }
            groups.add(front); groups.add(back);
        }
        // a facet whose speeds put GLASS on whichever side faces the lens center (so concave lenses are correct)
        Surface glassFacet(double x1,double y1,double x2,double y2,double glass,int grp){
            double tx=x2-x1,ty=y2-y1,L=Math.hypot(tx,ty)+1e-9, nx=ty/L, ny=-tx/L;   // same normal convention as discretize
            double mx=(x1+x2)/2,my=(y1+y2)/2, glassDot=(cx-mx)*nx+(cy-my)*ny;         // >0: glass on +normal (front) side
            Surface s = (glassDot>0) ? new Surface(x1,y1,x2,y2, AIR, glass)        // back=air, front=glass
                                     : new Surface(x1,y1,x2,y2, glass, AIR);       // back=glass, front=air
            s.group=grp; return s;
        }
    }

    // one interface line. mode 0 = dielectric (air|glass, index n), 1 = mirror (metal), 2 = absorbing wall.
    // reflection now comes from the Fresnel equations on the two media, not a hand-set coefficient.
    static final class EdSurface extends EdObj {
        static final double METAL_N=0.15, METAL_K=3.2;   // silver-ish complex index -> ~94% reflectance
        static final int GLASS=0, MIRROR=1, WALL=2;
        double x1,y1,x2,y2; int mode=WALL; double n=1.5;
        EdSurface(double x1,double y1,double x2,double y2,int mode){ this.x1=x1;this.y1=y1;this.x2=x2;this.y2=y2;this.mode=mode; }
        // legacy: -1 mirror, ~0 wall, +1 clear/glass -> map to a mode so old scenes/tests still build
        EdSurface(double x1,double y1,double x2,double y2,double type){ this(x1,y1,x2,y2, type<=-0.5?MIRROR : type>=0.5?GLASS : WALL); }
        double[][] handles(){ return new double[][]{{x1,y1},{x2,y2}}; }
        void dragHandle(int i,double x,double y){ if(i==0){x1=x;y1=y;} else {x2=x;y2=y;} }
        void moveBy(double dx,double dy){ x1+=dx;y1+=dy;x2+=dx;y2+=dy; }
        boolean hit(double x,double y){ return distSeg(x,y,x1,y1,x2,y2)<8; }
        void cycleMode(){ mode=(mode+1)%3; }
        void draw(Graphics2D g,boolean sel,double seg){
            Color c = mode==WALL? new Color(150,150,150) : mode==MIRROR? new Color(90,200,235) : new Color(150,200,255);
            g.setColor(c); g.setStroke(new BasicStroke(mode==MIRROR?3:mode==WALL?5:2));
            g.draw(new Line2D.Double(x1,y1,x2,y2)); drawHandles(g,this,sel);
            String lab = mode==WALL?"wall" : mode==MIRROR?"mirror" : String.format("glass n=%.2f", n);
            g.setColor(Color.LIGHT_GRAY); g.drawString(lab, (int)((x1+x2)/2+6), (int)((y1+y2)/2));
        }
        void build(java.util.List<Group> groups, java.util.List<Surface> loose, double seg){
            Surface s;
            if(mode==WALL){ s=new Surface(x1,y1,x2,y2, AIR, AIR); s.opaque=true; }
            else if(mode==MIRROR){ s=new Surface(x1,y1,x2,y2, AIR, 1.0/METAL_N); s.kappaFront=METAL_K; }  // air back | metal front
            else { s=new Surface(x1,y1,x2,y2, AIR, 1.0/n); }                                              // air back | glass front
            loose.add(s);
        }
    }

    // an arbitrary glass polygon (a triangle is a prism): N draggable vertices, glass inside, air outside.
    // double-click an edge to insert a vertex; double-click a vertex to delete it (min 3).
    static final class EdPolygon extends EdObj {
        double[] vx, vy; double n=1.6;
        EdPolygon(double[] vx,double[] vy){ this.vx=vx; this.vy=vy; }
        static EdPolygon regular(double cx,double cy,int sides,double r){
            double[] xs=new double[sides], ys=new double[sides];
            for(int i=0;i<sides;i++){ double a=-Math.PI/2 + 2*Math.PI*i/sides; xs[i]=cx+r*Math.cos(a); ys[i]=cy+r*Math.sin(a); }
            return new EdPolygon(xs,ys);
        }
        int nv(){ return vx.length; }
        double[][] handles(){ double[][] h=new double[nv()][]; for(int i=0;i<nv();i++) h[i]=new double[]{vx[i],vy[i]}; return h; }
        double area2(){ double s=0; int m=nv(); for(int i=0,j=m-1;i<m;j=i++) s+=(vx[j]-vx[i])*(vy[j]+vy[i]); return s; }  // shoelace (2x)
        // reject a vertex move that self-intersects the polygon or nearly collapses its area
        void dragHandle(int i,double x,double y){
            double ox=vx[i], oy=vy[i]; vx[i]=x; vy[i]=y;
            if(!isSimple() || Math.abs(area2())<3000){ vx[i]=ox; vy[i]=oy; }
        }
        void moveBy(double dx,double dy){ for(int i=0;i<nv();i++){ vx[i]+=dx; vy[i]+=dy; } }
        boolean hit(double x,double y){ return pointInPoly(x,y,vx,vy,nv()); }
        int nearVertex(double x,double y,double tol){ for(int i=0;i<nv();i++) if(Math.hypot(x-vx[i],y-vy[i])<tol) return i; return -1; }
        int nearEdge(double x,double y,double tol){ int m=nv();
            for(int i=0;i<m;i++){ int j=(i+1)%m; if(distSeg(x,y,vx[i],vy[i],vx[j],vy[j])<tol) return i; } return -1; }
        void insertVertex(int edge,double x,double y){ int m=nv(); int at=edge+1;
            double[] nx=new double[m+1], ny=new double[m+1];
            for(int i=0;i<at;i++){ nx[i]=vx[i]; ny[i]=vy[i]; }
            nx[at]=x; ny[at]=y;
            for(int i=at;i<m;i++){ nx[i+1]=vx[i]; ny[i+1]=vy[i]; }
            vx=nx; vy=ny;
        }
        void removeVertex(int i){ int m=nv(); if(m<=3) return;   // a polygon needs at least a triangle
            double[] nx=new double[m-1], ny=new double[m-1];
            for(int k=0,w=0;k<m;k++){ if(k==i) continue; nx[w]=vx[k]; ny[w]=vy[k]; w++; }
            vx=nx; vy=ny;
        }
        boolean isSimple(){ int m=nv();
            for(int i=0;i<m;i++){ double a1x=vx[i],a1y=vy[i],a2x=vx[(i+1)%m],a2y=vy[(i+1)%m];
                for(int j=i+1;j<m;j++){ if(j==(i+1)%m || (j+1)%m==i) continue;   // skip edges sharing a vertex
                    if(segProperCross(a1x,a1y,a2x,a2y, vx[j],vy[j],vx[(j+1)%m],vy[(j+1)%m])) return false; } }
            return true;
        }
        void draw(Graphics2D g,boolean sel,double seg){
            g.setColor(new Color(150,200,255,200)); g.setStroke(new BasicStroke(1.6f));
            int m=nv(); for(int i=0;i<m;i++) g.draw(new Line2D.Double(vx[i],vy[i],vx[(i+1)%m],vy[(i+1)%m]));
            drawHandles(g,this,sel);
            double gcx=0,gcy=0; for(int i=0;i<m;i++){ gcx+=vx[i]; gcy+=vy[i]; } gcx/=m; gcy/=m;
            g.setColor(new Color(180,210,255)); g.drawString(String.format("n=%.2f", n), (int)gcx-14, (int)gcy);
        }
        void build(java.util.List<Group> groups, java.util.List<Surface> loose, double seg){
            double glass=1.0/n; int m=nv(); Group faces=new Group(false);
            for(int i=0;i<m;i++){
                double ax=vx[i],ay=vy[i],bx=vx[(i+1)%m],by=vy[(i+1)%m];
                double tx=bx-ax,ty=by-ay,L=Math.hypot(tx,ty)+1e-9, nx=ty/L, ny=-tx/L;   // front = +normal
                double mx=(ax+bx)/2, my=(ay+by)/2;
                // step a hair along +normal; whichever side is INSIDE the polygon is the glass side (works for non-convex too)
                boolean glassFront = pointInPoly(mx+0.5*nx, my+0.5*ny, vx,vy,m);
                if(glassFront) faces.surfs.add(new Surface(ax,ay,bx,by, AIR, glass));   // speedFront=glass
                else            faces.surfs.add(new Surface(ax,ay,bx,by, glass, AIR));   // speedFront=air
            }
            groups.add(faces);
        }
    }

    // ---- handle / geometry helpers ----
    static void drawHandles(Graphics2D g, EdObj o, boolean sel){
        for(double[] h : o.handles()){
            g.setColor(sel?Color.WHITE:new Color(90,220,255));
            g.fillRect((int)h[0]-4,(int)h[1]-4,8,8);
            g.setColor(Color.BLACK); g.drawRect((int)h[0]-4,(int)h[1]-4,8,8);
        }
    }
    static double distSeg(double px,double py,double x1,double y1,double x2,double y2){
        double dx=x2-x1,dy=y2-y1, l2=dx*dx+dy*dy; if(l2<1e-9) return Math.hypot(px-x1,py-y1);
        double t=Math.max(0,Math.min(1,((px-x1)*dx+(py-y1)*dy)/l2));
        return Math.hypot(px-(x1+t*dx), py-(y1+t*dy));
    }
    static boolean pointInPoly(double px,double py,double[] xs,double[] ys,int nv){
        boolean in=false;
        for(int i=0,j=nv-1;i<nv;j=i++){
            if(((ys[i]>py)!=(ys[j]>py)) && (px < (xs[j]-xs[i])*(py-ys[i])/(ys[j]-ys[i])+xs[i])) in=!in;
        }
        return in;
    }
    // do segments a1-a2 and b1-b2 properly cross (not merely touch at an endpoint)?
    static boolean segProperCross(double a1x,double a1y,double a2x,double a2y,double b1x,double b1y,double b2x,double b2y){
        double d1=(a2x-a1x)*(b1y-a1y)-(a2y-a1y)*(b1x-a1x);
        double d2=(a2x-a1x)*(b2y-a1y)-(a2y-a1y)*(b2x-a1x);
        double d3=(b2x-b1x)*(a1y-b1y)-(b2y-b1y)*(a1x-b1x);
        double d4=(b2x-b1x)*(a2y-b1y)-(b2y-b1y)*(a2x-b1x);
        return ((d1>0)!=(d2>0)) && ((d3>0)!=(d4>0));
    }

    // ============================================================================ PANEL STATE
    final java.util.List<EdObj> objects = new ArrayList<>();
    EdObj sel; int dragH=-1; boolean dragBody=false; double lastX,lastY;
    boolean simMode=false; volatile boolean busy=false; BufferedImage simImg;
    double segMax = 5;         // segment length for ALL surfaces (slider). <= ~lambda/2 stays clean;
                               // larger = fewer/coarser emitters -> visible grating lobes on lens/prism/apertures
    int nWave = 21;            // number of wavelengths sampled across the visible band (configurable)
    boolean mono = false;      // monochromatic mode
    double monoNm = 550;       // wavelength (nm) when monochromatic
    int maxBounces = 6;        // recursion hard cap (configurable)
    double exposure = 18;      // fixed brightness divisor (higher = dimmer); scene-independent
    Runnable onSel = ()->{};   // notified when the selection changes (for the properties slider)

    void select(EdObj o){ sel=o; onSel.run(); }

    QuantumOptics(){
        setPreferredSize(new Dimension(DEFW,DEFH)); setBackground(Color.BLACK); setFocusable(true);
        objects.add(new EdLight(70,180,70,420));
        objects.add(new EdLens(330,300,150,80));
        MouseAdapter ma = new MouseAdapter(){
            public void mousePressed(MouseEvent e){ requestFocusInWindow();
                if(simMode){ simMode=false; repaint(); return; }
                double x=e.getX(), y=e.getY(); lastX=x; lastY=y; dragH=-1; dragBody=false;
                for(int oi=objects.size()-1; oi>=0; oi--){ EdObj o=objects.get(oi); double[][] hs=o.handles();
                    for(int i=0;i<hs.length;i++) if(Math.hypot(x-hs[i][0],y-hs[i][1])<9){ select(o); dragH=i; repaint(); return; } }
                for(int oi=objects.size()-1; oi>=0; oi--){ EdObj o=objects.get(oi); if(o.hit(x,y)){ select(o); dragBody=true; repaint(); return; } }
                select(null); repaint();
            }
            public void mouseDragged(MouseEvent e){ if(sel==null||simMode) return; double x=e.getX(),y=e.getY();
                if(dragH>=0) sel.dragHandle(dragH,x,y); else if(dragBody){ sel.moveBy(x-lastX,y-lastY); }
                lastX=x; lastY=y; repaint();
            }
            public void mouseReleased(MouseEvent e){ dragH=-1; dragBody=false; }
            public void mouseClicked(MouseEvent e){   // double-click a polygon: add a vertex on an edge, or delete one on a vertex
                if(simMode || e.getClickCount()!=2 || !(sel instanceof EdPolygon)) return;
                EdPolygon poly=(EdPolygon)sel; double x=e.getX(), y=e.getY();
                int vi=poly.nearVertex(x,y,9);
                if(vi>=0){ poly.removeVertex(vi); dragH=-1; repaint(); return; }
                int ei=poly.nearEdge(x,y,8);
                if(ei>=0){ poly.insertVertex(ei,x,y); dragH=-1; repaint(); }
            }
            public void mouseWheelMoved(MouseWheelEvent e){ if(simMode||sel==null) return;   // scroll to tweak index / type
                double d = -e.getPreciseWheelRotation();
                if(sel instanceof EdLens){ EdLens l=(EdLens)sel; l.n=clamp(l.n+0.03*d, N_MIN, N_MAX); }
                else if(sel instanceof EdPolygon){ EdPolygon p=(EdPolygon)sel; p.n=clamp(p.n+0.03*d, N_MIN, N_MAX); }
                else if(sel instanceof EdSurface){ EdSurface s=(EdSurface)sel; if(s.mode==EdSurface.GLASS) s.n=clamp(s.n+0.03*d, N_MIN, N_MAX); }
                else return;
                onSel.run(); repaint();
            }
        };
        addMouseListener(ma); addMouseMotionListener(ma); addMouseWheelListener(ma);
        getInputMap(WHEN_IN_FOCUSED_WINDOW).put(KeyStroke.getKeyStroke("DELETE"),"del");
        getInputMap(WHEN_IN_FOCUSED_WINDOW).put(KeyStroke.getKeyStroke("BACK_SPACE"),"del");
        getActionMap().put("del", new AbstractAction(){ public void actionPerformed(ActionEvent e){ deleteSelected(); }});
        getInputMap(WHEN_IN_FOCUSED_WINDOW).put(KeyStroke.getKeyStroke("M"),"mode");
        getInputMap(WHEN_IN_FOCUSED_WINDOW).put(KeyStroke.getKeyStroke("m"),"mode");
        getActionMap().put("mode", new AbstractAction(){ public void actionPerformed(ActionEvent e){
            if(sel instanceof EdSurface){ ((EdSurface)sel).cycleMode(); onSel.run(); simMode=false; repaint(); } }});
        // resizing the window changes the render size -> drop back to edit view so it's clear to re-Simulate
        addComponentListener(new ComponentAdapter(){ public void componentResized(ComponentEvent e){ if(simMode){ simMode=false; repaint(); } }});
    }
    static double clamp(double v,double lo,double hi){ return Math.max(lo,Math.min(hi,v)); }

    void deleteSelected(){ if(sel!=null && !(sel instanceof EdLight)){ objects.remove(sel); select(null); simMode=false; repaint(); } }
    void add(EdObj o){ objects.add(o); select(o); simMode=false; repaint(); }
    void createLens(){ add(new EdLens(360,300,130,70)); }
    void createSurface(){ add(new EdSurface(460,140,460,360, EdSurface.GLASS)); }   // press M to cycle glass/mirror/wall
    void createPolygon(){ add(EdPolygon.regular(430,300,3,100)); }   // a triangle of glass (a prism); drag/add/remove vertices

    Scene simScene;   // the last simulated scene (holds cached raw XYZ for instant re-exposure)
    void simulate(){ if(busy) return; busy=true; simMode=true; repaint();
        new Thread(()->{ try{ Scene sc=compile(); sc.build(); propagate(sc); simImg=render(sc); simScene=sc; }
            catch(Exception ex){ ex.printStackTrace(); } busy=false; repaint(); }).start();
    }
    // re-apply brightness to the cached field only -- no simulation recompute
    void retone(){ if(simScene==null||simScene.rdata==null) return; simScene.exposure=exposure; simImg=toneMap(simScene); repaint(); }

    // compile all editable objects into a Scene (+ source) for the recursive-branching engine
    Scene compile(){
        Scene sc=new Scene(); sc.name="scene"; sc.basePx=BASE_PX; sc.segLen=segMax; sc.maxBounces=maxBounces;
        sc.W = getWidth()>0?getWidth():DEFW; sc.H = getHeight()>0?getHeight():DEFH;   // render follows the window (headless -> default)
        sc.dispersive=true; sc.gamma=0.46; sc.pctile=0.985; sc.exposure=exposure;
        if(mono){ sc.wlNm=new double[]{monoNm}; }                       // monochromatic
        else { int n=Math.max(3,nWave); sc.wlNm=new double[n];          // white light: n samples across 400-700 nm
            for(int i=0;i<n;i++) sc.wlNm[i]=400+300.0*i/(n-1); }
        EdLight light=null; for(EdObj o:objects) if(o instanceof EdLight) light=(EdLight)o;
        if(light!=null) sc.setSource(light.x1,light.y1,light.x2,light.y2); else sc.setSource(1,20,1,sc.H-20);

        java.util.List<Group> groups=new ArrayList<>(); java.util.List<Surface> loose=new ArrayList<>();
        for(EdObj o:objects){ if(o instanceof EdLight) continue; o.build(groups, loose, segMax); }
        for(Group g:groups) sc.surfaces.addAll(g.surfs);       // lens / prism surfaces
        sc.surfaces.addAll(loose);                             // walls / mirrors

        detectSqueezes(sc);
        return sc;
    }

    // GENERAL squeeze detection (any angle): work in beam coordinates -- depth v along the beam,
    // width u across it. Cluster opaque surfaces into barriers by depth, project them onto the
    // width axis, and drop a spreading aperture into each unblocked gap the beam passes through.
    void detectSqueezes(Scene sc){
        double ax=sc.sax, ay=sc.say, tx=sc.stx, ty=sc.sty, dvx=sc.sdx, dvy=sc.sdy;
        java.util.List<Surface> occ=new ArrayList<>();
        for(Surface s:sc.surfaces) if(s.opaque || Math.max(s.kappaFront,s.kappaBack)>0.3) occ.add(s);   // walls & metals block the beam (glass transmits)
        occ.sort((a,b)->Double.compare(vmin(a,ax,ay,dvx,dvy), vmin(b,ax,ay,dvx,dvy)));
        int i=0;
        while(i<occ.size()){
            // one barrier = occluders whose depth ranges chain together (handles tilted barriers)
            double clMaxV=vmax(occ.get(i),ax,ay,dvx,dvy); int j=i+1;
            while(j<occ.size() && vmin(occ.get(j),ax,ay,dvx,dvy)-clMaxV < 20){ clMaxV=Math.max(clMaxV, vmax(occ.get(j),ax,ay,dvx,dvy)); j++; }
            java.util.List<double[]> cov=new ArrayList<>(); double vsum=0; boolean inBeam=false;
            for(int m=i;m<j;m++){ Surface s=occ.get(m);
                double u1=(s.x1-ax)*tx+(s.y1-ay)*ty, u2=(s.x2-ax)*tx+(s.y2-ay)*ty;
                double lo=Math.min(u1,u2), hi=Math.max(u1,u2);
                if(hi>0 && lo<sc.slen) inBeam=true;
                cov.add(new double[]{lo,hi});
                vsum += 0.5*(((s.x1-ax)*dvx+(s.y1-ay)*dvy)+((s.x2-ax)*dvx+(s.y2-ay)*dvy));
            }
            if(inBeam){
                double vbar=vsum/(j-i);
                cov.sort((a,b)->Double.compare(a[0],b[0]));
                double u=0;
                for(double[] iv:cov){ if(iv[0]>u) addAperture(sc,ax,ay,tx,ty,dvx,dvy,u,Math.min(iv[0],sc.slen),vbar);
                    u=Math.max(u,iv[1]); if(u>=sc.slen) break; }
                if(u<sc.slen) addAperture(sc,ax,ay,tx,ty,dvx,dvy,u,sc.slen,vbar);
            }
            i=j;
        }
    }
    static double vmin(Surface s,double ax,double ay,double dvx,double dvy){
        return Math.min((s.x1-ax)*dvx+(s.y1-ay)*dvy, (s.x2-ax)*dvx+(s.y2-ay)*dvy); }
    static double vmax(Surface s,double ax,double ay,double dvx,double dvy){
        return Math.max((s.x1-ax)*dvx+(s.y1-ay)*dvy, (s.x2-ax)*dvx+(s.y2-ay)*dvy); }
    void addAperture(Scene sc,double ax,double ay,double tx,double ty,double dvx,double dvy,double ua,double ub,double v){
        double w=ub-ua; if(w<1) return;
        // UNIFIED aperture: the opening is just a transmit-only (air|air) surface across the gap, split
        // into <= segMax pieces and discretized into Nyquist wavelets like any surface. All diffraction
        // -- the single-slit sinc, double-slit fringes -- EMERGES from the coherent sum of those wavelets.
        // (No analytic single-point sinc shortcut; the near field is now correct too, at more emitters.)
        int nseg=Math.max(1,(int)Math.ceil(w/segMax));
        for(int k=0;k<nseg;k++){
            double sa=ua+w*k/nseg, sb=ua+w*(k+1)/nseg;
            double p1x=ax+sa*tx+v*dvx, p1y=ay+sa*ty+v*dvy, p2x=ax+sb*tx+v*dvx, p2y=ay+sb*ty+v*dvy;
            sc.surfaces.add(new Surface(p1x,p1y,p2x,p2y, AIR, AIR));   // air|air -> Fresnel R=0,T=1 -> pure forward transmit
        }
    }

    @Override protected void paintComponent(Graphics g0){ super.paintComponent(g0);
        Graphics2D g=(Graphics2D)g0; g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        int cw=getWidth(), ch=getHeight();
        if(simMode){
            if(simImg!=null) g.drawImage(simImg,0,0,null); else { g.setColor(Color.BLACK); g.fillRect(0,0,cw,ch); }
            g.setColor(Color.WHITE); g.drawString(busy?"simulating...":"SIM  -  click canvas to return to edit", 12, ch-12);
        } else {
            g.setColor(new Color(16,16,22)); g.fillRect(0,0,cw,ch);
            for(EdObj o:objects) o.draw(g, o==sel, segMax);
            g.setColor(Color.WHITE);
            g.drawString("EDIT  -  drag handles (lens: ends scale, middle = thickness).  Scroll or slider = index/type.  Delete/button removes.", 12, 18);
        }
        drawScaleBar(g, cw, ch);
    }

    // reference measurement (bottom-right): a 100 px ruler + the wavelength scale
    static void drawScaleBar(Graphics2D g, int W, int H){
        int L=100, x0=W-40-L, y0=H-26;
        g.setColor(new Color(0,0,0,130)); g.fillRect(x0-10, y0-26, L+56, 46);
        g.setColor(Color.WHITE); g.setStroke(new BasicStroke(2)); g.setFont(new Font("SansSerif",Font.PLAIN,11));
        g.draw(new java.awt.geom.Line2D.Double(x0,y0,x0+L,y0));
        g.draw(new java.awt.geom.Line2D.Double(x0,y0-4,x0,y0+4));
        g.draw(new java.awt.geom.Line2D.Double(x0+L,y0-4,x0+L,y0+4));
        g.drawString(L+" px", x0+L/2-14, y0-7);
        g.setColor(new Color(150,210,255)); g.setStroke(new BasicStroke(3));
        g.draw(new java.awt.geom.Line2D.Double(x0, y0+12, x0+BASE_PX, y0+12));
        g.setColor(Color.WHITE);
        g.drawString(String.format("λ=%.0fpx", BASE_PX), x0+(int)BASE_PX+5, y0+16);
    }

    public static void main(String[] args) throws Exception {
        if (args.length>0 && args[0].equals("--headless") && args.length>1 && args[1].equals("edit")) {
            // exercise the editor compiler: walls->double slit (gap-fill) and a mirror (reflection)
            QuantumOptics p = new QuantumOptics();
            renderEd(p, "edit_lens");
            p.objects.clear();
            p.objects.add(new EdLight(70,120,70,480));
            p.objects.add(new EdSurface(300,40, 300,246, 0));
            p.objects.add(new EdSurface(300,254,300,346, 0));
            p.objects.add(new EdSurface(300,354,300,560, 0));
            renderEd(p, "edit_slit");
            p.objects.clear();                                 // WIDE gap -> should stay collimated (little spread)
            p.objects.add(new EdLight(70,120,70,480));
            p.objects.add(new EdSurface(300,40, 300,230, 0));
            p.objects.add(new EdSurface(300,370,300,560, 0));  // gap 230..370 = 140px wide
            renderEd(p, "edit_widegap");
            p.objects.clear();                                 // TILTED barrier double slit (was undetected before)
            p.objects.add(new EdLight(70,120,70,480));
            p.objects.add(new EdSurface(260,60,  330,250, 0));
            p.objects.add(new EdSurface(336,266, 344,288, 0));  // middle bar between the two slits (tilted line)
            p.objects.add(new EdSurface(350,304, 420,494, 0));
            renderEd(p, "edit_tiltslit");
            p.objects.clear();                                 // ROTATED source (beam right + slightly down) through a slit
            p.objects.add(new EdLight(200,90, 150,340));        // tilted light
            p.objects.add(new EdSurface(360,110, 360,280, 0));
            p.objects.add(new EdSurface(360,300, 360,470, 0));  // vertical slit, gap 280..300
            renderEd(p, "edit_rotsrc");
            p.objects.clear();
            p.objects.add(new EdLight(70,180,70,420));
            p.objects.add(new EdPolygon(new double[]{360,360,520}, new double[]{180,420,420}));   // right-triangle prism
            renderEd(p, "edit_prism");
            p.mono=true; p.monoNm=470; renderEd(p, "edit_prism_mono"); p.mono=false;
            p.objects.clear();                                 // concave (diverging) lens: negative thickness
            p.objects.add(new EdLight(70,180,70,420));
            EdLens cc=new EdLens(330,300,150,80); cc.t=-90; p.objects.add(cc);
            renderEd(p, "edit_concave");
            p.objects.clear();                                 // two lenses in series (between region should be stable)
            p.objects.add(new EdLight(70,190,70,410));
            p.objects.add(new EdLens(270,300,120,60));
            p.objects.add(new EdLens(600,300,120,60));
            renderEd(p, "edit_twolens");
            p.objects.clear();
            p.objects.add(new EdLight(70,180,70,420));
            p.objects.add(new EdSurface(560,140,470,360, -1)); // tilted mirror (type -1)
            renderEd(p, "edit_mirror");
            return;
        }
        SwingUtilities.invokeLater(()->{
            JFrame f=new JFrame("QuantumOptics - editor");
            f.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
            QuantumOptics panel=new QuantumOptics();
            JPanel bar=new JPanel(new FlowLayout(FlowLayout.LEFT,6,4)); bar.setBackground(new Color(32,32,40));
            JButton sim=new JButton("Simulate"); sim.addActionListener(e->panel.simulate());
            JButton bl=new JButton("Create Lens");    bl.addActionListener(e->panel.createLens());
            JButton bs=new JButton("Create Surface"); bs.addActionListener(e->panel.createSurface());
            JButton bpo=new JButton("Create Polygon"); bpo.addActionListener(e->panel.createPolygon());
            JButton del=new JButton("Delete");        del.addActionListener(e->panel.deleteSelected());
            bar.add(sim); bar.add(new JLabel(" | ")); bar.add(bl); bar.add(bs); bar.add(bpo); bar.add(new JLabel(" | ")); bar.add(del);
            JLabel seglab=new JLabel("seg "+(int)panel.segMax); seglab.setForeground(Color.WHITE);
            JSlider seg=new JSlider(4,120,(int)panel.segMax); seg.setPreferredSize(new Dimension(120,24));
            seg.addChangeListener(e->{ panel.segMax=seg.getValue(); seglab.setText("seg "+seg.getValue());
                panel.repaint();                                   // live: edit view re-facets as you drag
                if(!seg.getValueIsAdjusting() && panel.simMode) panel.simulate(); });  // re-run sim on release
            bar.add(new JLabel(" | ")); bar.add(seglab); bar.add(seg);

            // spectral controls: wavelength count, monochromatic toggle, bounce cap
            JLabel wlab=new JLabel("λ×"+panel.nWave); wlab.setForeground(Color.WHITE);
            JSlider wl=new JSlider(3,41,panel.nWave); wl.setPreferredSize(new Dimension(90,24));
            wl.addChangeListener(e->{ panel.nWave=wl.getValue(); wlab.setText("λ×"+wl.getValue()); });
            JCheckBox monoCb=new JCheckBox("mono"); monoCb.setForeground(Color.WHITE); monoCb.setOpaque(false);
            monoCb.addActionListener(e->{ panel.mono=monoCb.isSelected(); });
            JSpinner mnm=new JSpinner(new SpinnerNumberModel((int)panel.monoNm,380,700,10));
            mnm.setPreferredSize(new Dimension(64,24));
            mnm.addChangeListener(e->{ panel.monoNm=((Number)mnm.getValue()).doubleValue(); });
            JLabel blab=new JLabel("bounce"); blab.setForeground(Color.WHITE);
            JSpinner bsp=new JSpinner(new SpinnerNumberModel(panel.maxBounces,1,12,1));
            bsp.addChangeListener(e->{ panel.maxBounces=((Number)bsp.getValue()).intValue(); });
            bar.add(new JLabel(" | ")); bar.add(wlab); bar.add(wl); bar.add(monoCb); bar.add(mnm);
            bar.add(new JLabel(" | ")); bar.add(blab); bar.add(bsp);
            JLabel exlab=new JLabel("exp"); exlab.setForeground(Color.WHITE);
            JSlider ex=new JSlider(2,80,(int)panel.exposure); ex.setPreferredSize(new Dimension(90,24));
            ex.addChangeListener(e->{ panel.exposure=ex.getValue(); panel.retone(); });   // instant, no recompute
            bar.add(new JLabel(" | ")); bar.add(exlab); bar.add(ex);

            // properties strip: a slider that adapts to the selected object (index n, or surface type)
            JPanel props=new JPanel(new FlowLayout(FlowLayout.LEFT,8,4)); props.setBackground(new Color(24,24,30));
            JLabel plabel=new JLabel("select an object"); plabel.setForeground(Color.WHITE);
            JSlider slider=new JSlider(0,100,50); slider.setPreferredSize(new Dimension(260,24)); slider.setEnabled(false);
            props.add(plabel); props.add(slider);
            final boolean[] guard={false};
            panel.onSel = () -> { guard[0]=true;
                EdObj s=panel.sel;
                if(s instanceof EdLens || s instanceof EdPolygon){
                    double n = (s instanceof EdLens)?((EdLens)s).n : ((EdPolygon)s).n;
                    slider.setEnabled(true); slider.setValue((int)Math.round((n-N_MIN)/(N_MAX-N_MIN)*100));
                    plabel.setText(String.format("index  n = %.2f", n));
                } else if(s instanceof EdSurface){
                    EdSurface su=(EdSurface)s;
                    if(su.mode==EdSurface.GLASS){ slider.setEnabled(true); slider.setValue((int)Math.round((su.n-N_MIN)/(N_MAX-N_MIN)*100));
                        plabel.setText(String.format("glass  n = %.2f   (press M: glass/mirror/wall)", su.n)); }
                    else { slider.setEnabled(false); plabel.setText((su.mode==EdSurface.MIRROR?"mirror":"wall")+"   (press M to change: glass/mirror/wall)"); }
                } else { slider.setEnabled(false); plabel.setText(s==null?"select an object":"light (drag ends)"); }
                guard[0]=false;
            };
            slider.addChangeListener(e -> { if(guard[0]) return; EdObj s=panel.sel; double v=slider.getValue()/100.0;
                double nv = N_MIN + v*(N_MAX-N_MIN);
                if(s instanceof EdLens){ ((EdLens)s).n=nv; plabel.setText(String.format("index  n = %.2f",((EdLens)s).n)); }
                else if(s instanceof EdPolygon){ ((EdPolygon)s).n=nv; plabel.setText(String.format("index  n = %.2f",((EdPolygon)s).n)); }
                else if(s instanceof EdSurface && ((EdSurface)s).mode==EdSurface.GLASS){ ((EdSurface)s).n=nv; plabel.setText(String.format("glass  n = %.2f   (press M: glass/mirror/wall)",((EdSurface)s).n)); }
                panel.repaint();
            });

            JPanel north=new JPanel(new BorderLayout()); north.add(bar,BorderLayout.NORTH); north.add(props,BorderLayout.SOUTH);
            f.setLayout(new BorderLayout()); f.add(north,BorderLayout.NORTH); f.add(panel,BorderLayout.CENTER);
            f.pack(); f.setLocationRelativeTo(null); f.setVisible(true); panel.requestFocusInWindow();
        });
    }

    // headless helper: compile an editor panel to a Scene and write a preview PNG
    static void renderEd(QuantumOptics p, String tag) throws Exception {
        long t0=System.currentTimeMillis();
        Scene sc = p.compile(); sc.build(); propagate(sc);
        BufferedImage img = render(sc);
        Graphics2D g = img.createGraphics(); g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        for (EdObj o : p.objects) o.draw(g, false, p.segMax); drawScaleBar(g, sc.W, sc.H); g.dispose();
        javax.imageio.ImageIO.write(img, "png", new java.io.File("preview_"+tag+".png"));
        int el=0; for(Surface s:sc.surfaces) el+=s.n;
        System.out.printf("%s: surfaces=%d emitters=%d  %d ms -> preview_%s.png%n", tag, sc.surfaces.size(), el, System.currentTimeMillis()-t0, tag);
    }
}
