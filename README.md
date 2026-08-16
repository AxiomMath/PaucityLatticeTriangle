[![](logo.svg)](https://axiommath.ai/)

# Paucity of Lattice Triangles

This is a Lean formalization of the main theorem of *On the paucity of lattice triangles*.

## Main Results

* For every $\varepsilon > 0$ there is $c(\varepsilon) > 0$ such that
  $\\#\mathcal L_n / \\#\mathcal H_n \le c(\varepsilon) / n^{1-\varepsilon}$ for every integer $n \ge 5$,
  where $\mathcal H_n$ is the set of primitive obtuse rational triangles with denominator $n$
  and $\mathcal L_n$ the lattice (Veech) triangles among them, assuming the
  Larsen–Norton–Zykoski criterion (their Proposition 2.1, itself a consequence of
  Mirzakhani–Wright).

The constant depends only on $\varepsilon$ and is chosen before $n$. The criterion is carried
as an explicit hypothesis, and the lattice property is quantified over rather than defined;
everything else is proved from Mathlib. Nothing here is proved with `sorry` except the
challenge file below, where it is the point.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only depends on Mathlib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`, checking out the release matching this project's `lean-toolchain` (`v4.33.0-rc1`). Then, run the following command:
```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
