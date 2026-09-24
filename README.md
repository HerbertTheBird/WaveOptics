# WaveOptics

A 2D **wave-optics sandbox** in a single Java file. Light is modelled as a continuous complex field
(amplitude + phase), not as rays — so **refraction, focus, diffraction, dispersion, interference, and
reflection all emerge** from one simple rule rather than being coded in.

Everything is built from a single primitive: a **Surface** — a flat segment with a complex refractive
index (`n + iκ`) on each side. How much light reflects vs. transmits comes from the **Fresnel
equations** at the arrival angle, so a ~4% glass back-reflection, total internal reflection, and
metallic mirrors all fall out for free. You lay out objects in an editor, press **Simulate**, and it
computes the steady-state light field and renders it in true colour (CIE 1931 → sRGB).

![lens](https://raw.githubusercontent.com/HerbertTheBird/WaveOptics/main/docs/lens.png)

## Run

```sh
javac QuantumOptics.java
java QuantumOptics                 # interactive editor
java QuantumOptics --headless edit # render test-scene PNGs
```

Requires a JDK (17+ recommended). No dependencies.

## What you can build

| Object | What it is |
|---|---|
| **Light** | a plane-wave source (drag its two ends; the beam is perpendicular) |
| **Lens** | biconvex or biconcave (drag the middle handle past centre); focuses / diverges |
| **Polygon** | an arbitrary glass shape — starts as a **triangle** (a prism, disperses white light); double-click an edge to add a vertex, a vertex to remove it |
| **Surface** | one interface — press **M** to cycle **glass / mirror / wall** |
| **Double slit** | just walls with a gap; interference fringes emerge automatically |

## How it works

- Each surface is discretised into **Huygens point re-emitters** (spaced ≤ ½ wavelength).
- The source lights them; then they light each other in coherent **bounces**, each transfer split by
  Fresnel at its arrival angle.
- Every pixel sums the complex phasors reaching it (with exact occlusion); `|field|²` per wavelength
  composites in CIE XYZ, white-balanced to D65, then tone-mapped.
- Energy is conserved (verified via the true power flux `Im(U*·∂U/∂x)`, not `|field|²`).

## Controls

Drag handles to build objects; scroll or the properties slider to set index / mode. Sliders for
segment size, wavelength count (or monochromatic), bounce cap, and exposure. The render follows the
window size. **Simulate** runs the field; click the canvas to return to editing.
