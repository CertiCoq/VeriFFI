FROM yforster/coq:8.19.1--clang-11--compcert-3.13.1--extlib-0.12.1--equations-1.3--metacoq-1.3.1

MAINTAINER Joomy Korkut <joomy@type.systems>

RUN cd && git clone https://github.com/CertiCoq/VeriFFI && cd VeriFFI && git checkout 3f2b87aed2bad21f6d6513c9aa64fdecb5b351f6 && git submodule update --init --recursive
RUN cd ~/VeriFFI/certicoq && opam pin -n -y .
ENV PATH="/home/coq/.opam/2.1.5/bin:${PATH}"
RUN cd ~/VeriFFI/certicoq && opam install -y coq-certicoq --deps-only
RUN cd ~/VeriFFI/certicoq && opam install -y -v -j 4 coq-certicoq
RUN opam install -y coq-vst.2.14
RUN cd ~/VeriFFI/CertiGraph && make certigc
USER coq
RUN /bin/bash
