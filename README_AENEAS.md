This is how to extract Lean via Aeneas:
```
../aeneas/charon/bin/charon cargo --preset=aeneas
../aeneas/bin/aeneas -backend lean -dest proofs/GcdVerif ./gcd.llbc
```
THe resulting file must be adjusted to import TrailingZeros instead of axiomatizing it.