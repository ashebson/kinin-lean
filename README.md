# Kinnim in Lean

This project begins a formalization of *Seder Kinnim* with Mishnah Kinnim 1:1,
the first substantive passage indexed by the linked volume (page 14 of the
scan).

`Kinin.lean` models the two species, the two offering designations, and the two
altar levels. It checks the four stated rules and proves that using the other
level is always invalid. It also derives the symmetry behind the four cases:
changing either species or offering reverses the required level, while changing
both preserves it.

Check the formalization with:

```sh
lake build
```
