#!/usr/bin/env bash
# This BUILD file corresponds, more or less, to docker/Dockerfile
#RUN comments in this correspond, more or less, to commands in Dockerfile

OPAMJOBS ?= 1

# leave this out because it's linux-specific
# RUN sudo apt-get update && sudo apt-get install -y libgmp-dev

# let's not name the switch 4.10.2 because the user might have some other ocaml-4.10.2-purpose switch
# RUN opam switch create 4.10.2 && eval $(opam env)
echo "RUN: opam update"
opam update  # recommended
echo "RUN: opam switch create veriffi-coq8.19.1 4.14.1"
opam switch create veriffi-coq8.19.1 4.14.1  # this will fail if the switch already exists
echo "RUN: opam switch veriffi-coq8.19.1"
opam switch veriffi-coq8.19.1 # do this in case the previous command failed, harmless if succeeded
eval $(opam env --switch=veriffi-coq8.19.1)

# RUN opam repo add coq-released http://coq.inria.fr/opam/released && opam pin add coq 8.19.1
echo "RUN: opam repo add coq-released http://coq.inria.fr/opam/released"
opam repo add coq-released https://coq.inria.fr/opam/released
echo "RUN: opam pin add coq 8.19.1"
opam pin add coq 8.19.1 -y || exit 1
echo "RUN: opam pin add coqide 8.19.1"
opam pin add coqide 8.19.1 -y # all right if this one fails

echo "RUN: git submodule update --init --checkout --recursive"
git submodule update --init --checkout --recursive  || exit 1

# certicoq is now a submodule of veriffi
#  RUN cd && git clone https://github.com/joom/certicoq && cd ~/certicoq && git checkout coq-8.15 && git submodule update --init

# no longer need metacoq from submodule, since certicoq uses the opam release of metacoq
# echo "RUN: cd certicoq; opam pin -n -y submodules/metacoq"
# (cd certicoq; opam pin -n -y submodules/metacoq) || exit 1
echo "RUN: cd certicoq; opam pin -n -y . || exit 1"
(cd certicoq; opam pin -n -y .) || exit 1
echo "RUN: cd certicoq; opam install coq-certicoq --deps-only -y || exit 1"
(cd certicoq; opam install coq-certicoq --deps-only -y) || exit 1
echo "RUN: clang --version"
clang --version || exit 1

# RUN cd ~/certicoq && opam install .
echo "RUN: cd certicoq; opam install ."
(cd certicoq; opam install . -y) || exit 1

echo "RUN: opam install coq-vst.2.14"
opam install coq-vst.2.14 -y || exit 1
echo "RUN: opam install coq-vst-lib.2.14"
opam install coq-vst-lib.2.14 -y || exit 1

echo "RUN: cd CertiGraph; make -j $(OPAMJOBS) certigc"
(cd CertiGraph; make -j $(OPAMJOBS) certigc) || exit 1


# Now build VeriFFI itself
echo "RUN: make -kj $(OPAMJOBS)"
make -kj $(OPAMJOBS) || exit 1

# USER opam
# RUN /bin/bash
