# Building

```
cd lib/tlc/
make                 # for vio output
# env SERIOUS=1 make # for vo output

cd ../..
./configure
make quick      # for vio output
make J=5 vio2vo # for turning vio output into vo output
# make          # for vo output
```

(Sorry that this is not more automated, but I can't for the life of mine
figure out the incantation that makes coq\_makefile behave sensibly.)


# Development

If you use Coqide or Proof General, make sure they honor the settings from
`\_CoqProject` (generated by `./configure`).
