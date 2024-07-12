

Work-in-progress of verification. Can be run as described in the ``Install.md`` file in the main directory.

- Example for nat/list in ``example`` directory:
  - ``glue.h``: Glue code generate file for nat/list.
  - ``glue.c``: Adapted version of glue code which is generated for nat/list. All adaptions are listed in the document.
  - ``glue.v``: The CompCert-generated file of ``glue.c``.
- ``graph_add.v`` : Augments CertiGraph with functions for adding a new node at the end of a generation (in contrast to previously copying an already available graph). This requires changing the graph/compatibility condtions/proofs that the generated graph is still well-generated to be able to interact e.g. with the garbage collector
- ``demo``: Example specifications for ``nat`` and ``list``, non-general approach but the one later used
- ``specs_library.v``: General definitions for specifications, needed both for specific specifications and general specifications
- ``specs_general.v``: General specification built on a general specification of constructors
- ``proofs_library_general.v``: General lemmas needed to prove glue code correct (only in verif branch)
- ``alloc_proof_general.v``: Subsumption approach. A general definition of the general Clight representation, a general Clight proof, and a work-in-progress general subsumption proof. (only in verif branch)

