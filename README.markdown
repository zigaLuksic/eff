EEFF
===

EEFF is an extension of Eff with local algebraic effect theories. The instalation steps are the same as for regular Eff and described below.  

For the basic understanding of algebraic handlers we recommend a quick glance at the examples of the `master` branch. For an introduction to the syntax of local effect theories there are multiple examples provided, with `examples/intro_to_theories.eff` serving as a short guide.

EEFF has been [formalised](https://github.com/zigaLuksic/eeff-formalization) in the Coq proof assistant.

A simple code highlighting extension for VSCode is included in `etc/EEFF-vscode`. The instalation instruction are in the file `etc/EEFF-vscode/installing-extension.md`.

Installation & Usage
--------------------

### Prerequisites

We have tested Eff on Mac OS X and Linux, and it should work on other
Unix-like systems. In principle, nothing prevents Eff from running
on Windows, we just have not tested it yet.

To install Eff, you need a standard Unix-style build environment as well as

1. [OCaml](https://ocaml.org/), version 4.06 or newer,
2. [Menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator, and
3. [js_of_ocaml](http://ocsigen.org/js_of_ocaml/) OCaml to Javascript compiler.

We do not require, but recommend a command-line editing wrapper such as
[rlwrap](http://freecode.com/projects/rlwrap) or
[ledit](http://cristal.inria.fr/~ddr/ledit/). Eff uses these automatically.

### Installing with OPAM

This is the easiest way to install Eff. Follow these steps:

1. Install the [OPAM package manager](http://opam.ocamlpro.com) if you do not have it yet.

2. Make sure you have the correct OCaml compiler activated. Since Eff compiles with all recent version of OCaml you probably need not worry about this step.

3. Run

        opam pin add -k git eff https://github.com/matijapretnar/eff.git

   OPAM will download and build the necessary dependencies first, then download
   and build Eff itself.

### Manual installation

To compile Eff manually, first clone the GitHub repository

    git clone https://github.com/matijapretnar/eff.git
    cd eff

and run

    ./configure

If it complains you will have to install missing prerequisites. In case of
problems, `make clean distclean` might help. The configuration script takes
standard GNU Autoconf arguments, such as `--prefix` which determines where to
install Eff. Type `./configure --help` for more information. Next, run

    make

If all goes well, you should be able to run Eff in-place by typing `./eff`.

You can also run a battery of tests with

    make test

Finally, to install the command `eff`, run

    sudo make install

See the file `etc/README.txt` for editor support.

### Using Eff

There are examples of Eff in `examples` subdirectory that should get you started. The Eff
syntax is very close to that of OCaml. You can find further material about Eff on the [Eff page](http://www.eff-lang.org/).

Copyright and license
---------------------

Copyright (c) 2015, Andrej Bauer and Matija Pretnar
Copyright (c) 2012, Timotej Lazar

Eff is distributed under the abbreviated BSD License, see `LICENSE.txt` for
licensing information.
