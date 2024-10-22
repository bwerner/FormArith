# MPRI's 2.7.1 course

## Setup

To use this project, you will need to install some specific dependencies in order to have a development setup of this project.

There are two maintained ways to do this, using `nix` (preferred) or `opam`.


### Setup using `nix` flakes

We assume that you have `nix` installed on your system. Setup instructions can be found here: <https://nixos.org/download>.

To setup the project for development purposes, you can use `nix develop` to enter an interactive subshell containing the tools you will need:

```bash
cd <form-arith>
nix develop
``` 

The tools lives in this subshell and will disappear as soon as you leave the subshell.

If you do not have flakes enabled, you may get this error:

```txt
error: experimental Nix feature 'nix-command' is disabled; use ''--extra-experimental-features nix-command' to override
```

All you have to do is enable flakes, see this [NixOS wiki page](https://nixos.wiki/wiki/Flakes) for more details on how to enable flakes permanently.


### Setup using `opam`

We assume that you have `opam` installed on your system. Setup instructions can be found here: https://opam.ocaml.org/doc/Install.html

1. Create a new `opam` switch for this project:

```bash
opam switch create <name> --packages=ocaml-variants.4.14.2+options,ocaml-option-flambda
opam switch <name>
```

2. Install the necessary dependencies:

```bash
opam pin add coq 8.19.2
opam repo add coq-released https://coq.inria.fr/opam/released
```

3. Build the Rocq implementation of the type system:

```bash
dune build
```

