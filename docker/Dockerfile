FROM yforster/coq:8.17.0--clang-11--compcert-3.12--extlib-0.11.8--equations-1.3--elpi.1.17.1-metacoq-8.17.dev.e0794e3

MAINTAINER Joomy Korkut <joomy@cs.princeton.edu>

RUN cd && git clone https://github.com/CertiCoq/VeriFFI && cd VeriFFI && git checkout 40167e4aa5b15114c2d09d554d32caa3583b9033 && git submodule update --init --recursive
RUN cd ~/VeriFFI/certicoq && opam pin -n -y .
ENV PATH="/home/coq/.opam/4.13.1+flambda/bin:${PATH}"
RUN cd ~/VeriFFI/certicoq && opam install -y coq-certicoq --deps-only
RUN cd ~/VeriFFI/certicoq && opam install -y -v -j 4 coq-certicoq
RUN opam install -y coq-vst.2.12
RUN cd ~/VeriFFI/CertiGraph && make clightgen && make BITSIZE=64 -j4 CertiGC/gc_correct.vo CertiGC/gc_spec.vo
USER coq
RUN /bin/bash
