# Building

```
git submodule init
git submodule update

cd lib/tlc/
env SERIOUS=1 make -j5   # for vo output; 5 is the number of concurrent jobs
# make -j5               # for vio output

cd ../..
./configure
make -j5                 # for vo output
# make -j5 quick         # for vio output
# make J=5 vio2vo        # for turning vio output into vo output
```

(Sorry that this is not more automated, but I can't for the life of mine
figure out the incantation that makes coq\_makefile behave sensibly.)


# Development

If you use CoqIDE or Proof General, make sure they honor the settings from
`\_CoqProject` (generated by `./configure`).


# License

Your use of this software is governed by the MIT license, a copy of which may
be found in the LICENSE file.

This repository also contains a modified copy of Arthur Charguéraud's TLC
library, licensed under the CeCILL-B license.
