// A surface is a flat segment -- the one and only optical primitive. It carries a complex refractive
// index on each side (real part from the light SPEED, imaginary part `kappa` = absorption) and is
// subdivided into omnidirectional point re-emitters, each storing complex amplitude emitted to its
// front (+normal) and back (-normal) half-space. Reflection/transmission come from the Fresnel
// equations (see QuantumOptics.buildFresnel), which populate the per-wavelength frF/frB tables.
final class Surface {
    final double x1, y1, x2, y2;
    double speedFront, speedBack;     // light speed on +normal (front) / -normal (back) side; n = 1/speed
    double kappaFront=0, kappaBack=0; // imaginary index (absorption) per side: 0 dielectric, >0 metal/lossy
    boolean opaque=false;             // hard absorbing wall: no reflection, no transmission
    // per-wavelength Fresnel tables (rebuilt each wavelength), indexed by cos(incidence)*128:
    double[][] frF, frB;              // [bin] = {reflect_re, reflect_im, transmit_re, transmit_im}; incident from front / back
    int group = -1;                    // facets of one optical face share a group; they don't self-shadow

    int n;
    double[] ex, ey, nx, ny, wgt;     // element center, unit normal (front dir), width weight
    // per wavelength [w][e] complex amplitude, front/back half-space:
    double[][] tFr,tFi,tBr,tBi;       // TOTAL emitted (summed over bounces) -> used by the renderer
    double[][] pFr,pFi,pBr,pBi;       // this bounce's newly-emitted delta -> propagated to next bounce
    double[][] iFr,iFi,iBr,iBi;       // incoming accumulator for the current bounce

    Surface(double x1,double y1,double x2,double y2,double speedBack,double speedFront) {
        this.x1=x1; this.y1=y1; this.x2=x2; this.y2=y2;
        this.speedBack=speedBack; this.speedFront=speedFront;
    }

    void discretize(double lambdaMinPx, double spacing) {
        double len = Math.hypot(x2-x1, y2-y1);
        double tx = (x2-x1)/(len+1e-9), ty = (y2-y1)/(len+1e-9);
        // NYQUIST: emitters must be <= half the shortest wavelength IN THIS SURFACE'S medium
        // (the slower/denser side has the shortest wavelength), else short wavelengths alias.
        double nyq = QuantumOptics.NYQ_FRAC * lambdaMinPx * Math.min(speedFront, speedBack);
        double eff = Math.min(spacing, nyq);
        int m = Math.max(1, (int)Math.round(len / eff));
        n = m; wgt = new double[n]; ex = new double[n]; ey = new double[n];
        double ds = len / m;
        for (int k = 0; k < m; k++) {
            double t = (k + 0.5) / m;
            ex[k] = x1 + t*(x2-x1); ey[k] = y1 + t*(y2-y1); wgt[k] = ds;
        }
        double cnx = ty, cny = -tx;                      // unit normal perpendicular to the segment
        double L = Math.hypot(cnx, cny) + 1e-9;
        nx = new double[n]; ny = new double[n];
        for (int i = 0; i < n; i++) { nx[i]=cnx/L; ny[i]=cny/L; }
    }
    void alloc(int nw){
        tFr=new double[nw][n]; tFi=new double[nw][n]; tBr=new double[nw][n]; tBi=new double[nw][n];
        pFr=new double[nw][n]; pFi=new double[nw][n]; pBr=new double[nw][n]; pBi=new double[nw][n];
        iFr=new double[nw][n]; iFi=new double[nw][n]; iBr=new double[nw][n]; iBi=new double[nw][n];
        frF=new double[QuantumOptics.FBINS][4]; frB=new double[QuantumOptics.FBINS][4];
    }
}
