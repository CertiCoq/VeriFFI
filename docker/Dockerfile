FROM yforster/coq:8.17.0--clang-11--compcert-3.12--extlib-0.11.8--equations-1.3--elpi.1.17.1

MAINTAINER Joomy Korkut <joomy@cs.princeton.edu>

RUN cd && git clone https://github.com/CertiCoq/VeriFFI && cd VeriFFI && git submodule update --init --recursive
RUN cd ~/VeriFFI/certicoq && opam pin -n -y .
ENV PATH="/home/coq/.opam/4.13.1+flambda/bin:${PATH}"
RUN cd ~/VeriFFI/certicoq && opam install -y coq-certicoq --deps-only
RUN cd ~/VeriFFI/certicoq && opam install -y -v -j 4 coq-certicoq
RUN opam install -y coq-vst.2.12
# RUN cd ~/VeriFFI/CertiGraph && make BITSIZE=64 -j4 certigc
USER coq
RUN /bin/bash
# RUN cd ~/VeriFFI/CertiGraph && git checkout 1be51414c139f8bc16b3e22f72989e454c37ce3c 
