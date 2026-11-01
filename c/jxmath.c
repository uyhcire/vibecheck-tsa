/* libm entry points for JsbExact's Float instance, kept out of Lean's C so clang cannot merge sin/cos. */
#include <math.h>

double jx_sin(double x) { return sin(x); }
double jx_cos(double x) { return cos(x); }
/* Darwin's combined sin/cos, which clang substitutes when one C function computes both of the same argument. */
#ifdef __APPLE__
double jx_sincos_sin(double x) { return __sincos_stret(x).__sinval; }
double jx_sincos_cos(double x) { return __sincos_stret(x).__cosval; }
#else
/* No __sincos_stret off Darwin; plain sin/cos link but are not claimed bit-exact against JSBSim. */
double jx_sincos_sin(double x) { return sin(x); }
double jx_sincos_cos(double x) { return cos(x); }
#endif
