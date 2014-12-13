Actor Verification Library
==========================

This is a library to formalize and verify Actor systems on Coq.


Requirements
------------

- Coq 8.4pl5


Install
-------

```sh
$ cd /path/to/coq-actor
$ make
$ make install
```


Examples
--------

See [`examples`](./examples) directory.


Current status
--------------

- [x] Convenient notation
    + syntax.v
- [x] Proof of no duplication of Actor names
    + trans_invariant.v (`initial_trans_star_no_dup`)
- [ ] Mechanism to verify Actor systems
- [ ] Communication between configurations
- [ ] Extraction to Erlang
- [ ] Supervisor / Monitor / Link
