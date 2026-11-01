# ci-proof log (one line per commit: what was proved / built, what remains)

- 6deb7a9 | law: lawfirst p1 with a continuous speed term and a throttle schedule above 2500 m (climb ends at an exact Fx fixed point, 2619.4 m); numerics harness | remains: everything
- b75aa80 | T v1: Lyapunov ellipsoid on 7 slow coordinates around the climb manifold + slaved fast coordinates; official 1.5061 (coverage 0.9941), 0 counterexamples | T not invariant (fast tolerances)
- 0e7900e | proved: PSD quadratic-form lemmas (Cauchy–Schwarz, triangle inequality, `contract_step`) | —
- 5fdb2bc | proved: `tInvariant_of_lyap`, generic reduction of `TInvariant` to bridge + model obligations | —
- 3e7343e | skeleton: `Skel.tinv : TInvariant lawT` from 6 sorry'd obligations; `P_psd` proved from `pNode_psd` | sorry: pNode_psd, inT_sound, inT_complete, tick_safe_climb, tick_side, tick_encl
- 95d1ff3 | law v3 (qRef from the kinematic nEst: inside T the law reads no stored acceleration field); T v2 (frozen-h centre, sampled-Jacobian LMI rho 0.9924, altitude-dependent tolerances); official 1.5057 (coverage 0.9894) | T fails at the fast-tolerance corners (kinks of the lift/drag tables)
- 00577f7 | T v3: kink-aware fast constraints (one loose direction k(h), rest tight); 16730 exact-inT samples + adversarial search, 0 exits; official 1.5057, 0 counterexamples | top band too tight for interval safety
- 7f572de, 2d48ac1 | T v4: r = 4.5, tolerance margin 1.25, redundant 50 m cell boxes in inT; LawIv/SafeIv interval checkers; 19005 samples + adversarial, 0 exits (worst ratio 0.979); interval safety passes on every cell | proofs of tick_safe_climb in progress
