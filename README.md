<p><img src="https://github.com/CertiCoq/VeriFFI/blob/main/doc/VeriFFI.png" alt="VeriFFI" width="400px"/>
</p>

VeriFFI is a verified Foreign Function Interface (FFI) for Coq (Gallina) programs that call, and are called by, C programs.  The operational connection is by compiling Gallina programs through C using the CertiCoq compiler.  The specification/verification connection is by using the Verified Software Toolchain (Verifiable C) to specify library functions written in C that are callable by CertiCoq-compiled programs, and vice versa.  The goal is to have a fully foundational soundness proof for this connection. This is still a work in progress.
