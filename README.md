# Data Types with Symmetries via Action Containers

## Abstract

We study two kinds of containers for data types with symmetries in homotopy type theory, and clarify their relationship by introducing the intermediate notion of action containers.
Quotient containers are set-valued containers with groups of permissible permutations of positions, interpreted as analytic functors on the category of sets.
Symmetric containers encode symmetries in a groupoid of shapes, and are interpreted accordingly as polynomial functors on the 2-category of groupoids.

Action containers are endowed with groups that act on their positions, with morphisms preserving the actions.
We show that, as a category, action containers are equivalent to the free coproduct completion of a category of group actions.
We derive that they model non-inductive single-variable strictly positive types in the sense of Abbott et al.:
The category of action containers is closed under arbitrary (co)products and exponentiation with constants.
We equip this category with the structure of a locally groupoidal 2-category, and prove that this corresponds to the full 2-subcategory of symmetric containers whose shapes have pointed connected components.
This follows from the embedding of a 2-category of groups into the 2-category of groupoids, extending the delooping construction.

## This Repository

This repository contains the Agda mechanization of our development of _action containers_.

The code depends on the Agda [`cubical`](https://github.com/agda/cubical) library, v0.7,
and (for now), Max New's [`cubical-categorical-logic`](https://github.com/maxsnew/cubical-categorical-logic).

The recommended way to type check and investigate this library is via [Nix](https://nixos.org/download/).
To type check all modules, run:

```console
$ nix build
```

To enter a reproducible development shell, with all dependencies available, run

```console
$ nix shell
nix-shell> # Get current version of Agda
nix-shell> which agda
/nix/store/l9826w9y9lg2yyap3zz6xjxskmg5cnk1-agdaWithPackages-2.7.0/bin/agda
nix-shell> agda --version
Agda version 2.7.0
```

To interactively type check all source modules in a development shell, run

```console
nix-shell> # Generate Everything.agda with a list of all modules
nix-shell> ./gen-everything.sh
nix-shell> agda Everything.agda
```

To render all source modules included from `README.agda` to static HTML pages, run

```console
$ nix build '.#default.html'
```

The directory `./result-html` will contain the rendered pages, with `README.agda` available as `./result-html/README.html`.

## License

All source code in this repository is licensed under the terms of the MIT License, see [LICENSE](./LICENSE).
