FROM ocaml/opam

MAINTAINER Joomy Korkut <joomy@cs.princeton.edu>

RUN sudo apt-get update
RUN sudo apt-get install -y libgmp-dev
RUN opam switch create 4.07.1
RUN eval $(opam env)
ENV PATH="/home/opam/.opam/4.07.1/bin:${PATH}"
RUN opam repo add coq-released http://coq.inria.fr/opam/released
RUN opam pin add coq 8.13.2
RUN opam install coq-flocq.3.4.2
RUN opam install coq-compcert.3.9
RUN cd && git clone https://github.com/PrincetonUniversity/VST
RUN cd ~/VST && git checkout 0d6c15953caff1c97a4416f26272eac578ac6321 && make BITSIZE=64 && make install
RUN cd && git clone https://github.com/MetaCoq/metacoq.git && cd metacoq && git checkout 332c0c8d5308297952fe60c2fb81100e0c488c39
RUN cd ~/metacoq && opam install . --deps-only 
RUN cd ~/metacoq && ./configure.sh local
RUN cd ~/metacoq && make && make install && cd
RUN opam install coq-ext-lib.0.11.5
RUN cd && git clone https://github.com/Salamari/CertiGraph.git && cd CertiGraph
RUN cd ~/CertiGraph && make BITSIZE=64 -j4 && make BITSIZE=64 install
# CERTICOQ DOESN'T WORK YET
# RUN cd && git clone https://github.com/intoverflow/certicoq.git && cd certicoq && git checkout -b prims origin/prims
# RUN cd ~/certicoq && make all
# RUN cd ~/certicoq && sudo make -j4
# RUN cd ~/certicoq && sudo sh ./make_plugin.sh
# RUN cd ~/certicoq && sudo make install
USER opam
RUN /bin/bash
