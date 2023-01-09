FROM ocaml/opam

MAINTAINER Joomy Korkut <joomy@cs.princeton.edu>

RUN sudo apt-get update && sudo apt-get install -y libgmp-dev
RUN opam switch create 4.09.1 && eval $(opam env)
ENV PATH="/home/opam/.opam/4.09.1/bin:${PATH}"
RUN opam repo add coq-released http://coq.inria.fr/opam/released && opam pin add coq 8.15.2
RUN cd && git clone https://github.com/certicoq/certicoq && cd ~/certicoq && git checkout 12b7277f088de0c9b92fe56a2d11e740d8c9f3a4 && git submodule update --init
RUN cd ~/certicoq && opam pin -n -y submodules/metacoq && opam pin -n -y . && opam install coq-certicoq --deps-only && sudo apt-get --assume-yes install clang
RUN cd ~/certicoq && opam install coq-certicoq
RUN cd && git clone https://github.com/PrincetonUniversity/VST && cd ~/VST && git checkout 013640e9837c0cdbe03d38a7f318171b01aaca87 && make BITSIZE=64 && make install
RUN cd && git clone https://github.com/CertiGraph/CertiGraph && cd ~/CertiGraph && git checkout 1be51414c139f8bc16b3e22f72989e454c37ce3c 
RUN cd ~/CertiGraph && make BITSIZE=64 -j4 certigc
USER opam
RUN /bin/bash
