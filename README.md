<p><img src="https://github.com/CertiCoq/VeriFFI/blob/main/doc/VeriFFI.png" alt="VeriFFI" width="400px"/>
</p>

VeriFFI is a verified Foreign Function Interface (FFI) for Coq (Gallina) programs that call, and are called by, C programs.  The operational connection is by compiling Gallina programs through C using the CertiCoq compiler.  The specification/verification connection is by using the Verified Software Toolchain (Verifiable C) to specify library functions written in C that are callable by CertiCoq-compiled programs, and vice versa.  The goal is to have a fully foundational soundness proof for this connection. This is still a work in progress.

Participants:
- [Andrew W. Appel](https://www.cs.princeton.edu/~appel/)
- [Joomy Korkut](https://www.cs.princeton.edu/~ckorkut/)
- [Kathrin Stark](https://www.k-stark.de/)

Journal Article:
- [A Verified Foreign Function Interface between Coq and C](https://doi.org/10.1145/3704860), by Joomy Korkut, Kathrin Stark, and Andrew W. Appel,  _Proc. ACM Program. Lang._ 9, POPL, Article 24 (January 2025), 31 pages.

PhD Thesis:
- [_Foreign Function Verification Through Metaprogramming_](http://arks.princeton.edu/ark:/88435/dsp01k930c143z), by Joomy Korkut, PhD Thesis, Princeton University, October 2024.
