#!/usr/bin/env bash
# This BUILD file corresponds, more or less, to docker/Dockerfile
#RUN comments in this correspond, more or less, to commands in Dockerfile

# leave this out because it's linux-specific
# RUN sudo apt-get update && sudo apt-get install -y libgmp-dev

# let's not name the switch 4.10.2 because the user might have some other ocaml-4.10.2-purpose switch
# RUN opam switch create 4.10.2 && eval $(opam env)
echo "RUN: opam update"
opam update  # recommended
echo "RUN: opam switch create veriffi-coq8.17.1 4.14.1"
opam switch create veriffi-coq8.17.1 4.14.1  # this will fail if the switch already exists
echo "RUN: opam switch veriffi-coq8.17.1"
opam switch veriffi-coq8.17.1 # do this in case the previous command failed, harmless if succeeded
eval $(opam env --switch=veriffi-coq8.17.1)

# we don't need a shell command for this because it's part of "eval $(opam env)" above
# ENV PATH="/home/opam/.opam/4.10.2/bin:${PATH}"

# RUN opam repo add coq-released http://coq.inria.fr/opam/released && opam pin add coq 8.17.1
echo "RUN: opam repo add coq-released http://coq.inria.fr/opam/released"
opam repo add coq-released https://coq.inria.fr/opam/released
echo "RUN: opam pin add coq 8.17.1"
opam pin add coq 8.17.1 || exit 1
echo "RUN: opam pin add coqide 8.17.1"
opam pin add coqide 8.17.1  # all right if this one fails

echo "RUN: git submodule update --init --checkout --recursive"
git submodule update --init --checkout --recursive  || exit 1

# certicoq is now a submodule of veriffi
#  RUN cd && git clone https://github.com/joom/certicoq && cd ~/certicoq && git checkout coq-8.15 && git submodule update --init

# can we separate the "clang" part into another line, and then comment out out?
# RUN cd ~/certicoq && opam pin -n -y submodules/metacoq && opam pin -n -y . && opam install coq-certicoq --deps-only && sudo apt-get --assume-yes install clang
echo "RUN: cd certicoq; opam pin -n -y submodules/metacoq"
(cd certicoq; opam pin -n -y submodules/metacoq) || exit 1
echo "RUN: cd certicoq; opam pin -n -y . || exit 1"
(cd certicoq; opam pin -n -y .) || exit 1
echo "RUN: cd certicoq; opam install coq-certicoq --deps-only -y || exit 1"
(cd certicoq; opam install coq-certicoq --deps-only -y) || exit 1
echo "RUN: clang --version"
clang --version || exit 1

# RUN cd ~/certicoq && opam install coq-certicoq
echo "RUN: cd certicoq; opam install coq-certicoq"
(cd certicoq; opam install coq-certicoq) || exit 1

# we are using coq-vst.2.11.1 instead of that commit 013640e (which is coq-vst-2.11),
# and we're installing from the opam coq-released repository instead of just "make"
# RUN cd && git clone https://github.com/PrincetonUniversity/VST && cd ~/VST && git checkout 013640e9837c0cdbe03d38a7f318171b01aaca87 && make BITSIZE=64 && make install
echo "RUN: opam install coq-vst.2.12"
opam install coq-vst.2.12 || exit 1

# the CertiGraph submodule of VeriFFI us currently at commit 1be51414c139f8bc16b3e22f72989e454c37ce3c 
# RUN cd && git clone https://github.com/CertiGraph/CertiGraph && cd ~/CertiGraph && git checkout 1be51414c139f8bc16b3e22f72989e454c37ce3c 

echo "RUN: cd CertiGraph; make clightgen"
(cd CertiGraph; make clightgen) || exit 1
echo "RUN: cd CertiGraph; make -j4 CertiGC/gc_correct.vo CertiGC/gc_spec.vo"
(cd CertiGraph; make -j4 CertiGC/gc_correct.vo CertiGC/gc_spec.vo) || exit 1

# Now build VeriFFI itself
echo "RUN: make -kj4"
# make -kj4 || exit 1

# USER opam
# RUN /bin/bash
