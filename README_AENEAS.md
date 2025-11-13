This is how to extract Lean via Aeneas:
```
../aeneas/charon/bin/charon cargo --preset=aeneas
../aeneas/bin/aeneas -backend lean -dest proofs/GcdVerif -split-files ./gcd.llbc
```

TH `split-files` option allows us to define our own library functions, in particular the function `trailing_zeros` that is missing.