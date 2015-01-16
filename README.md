Actor Verification Framework
============================

[![wercker status](https://app.wercker.com/status/fd8f4cf437b7230524c5d00e99858456/m "wercker status")](https://app.wercker.com/project/bykey/fd8f4cf437b7230524c5d00e99858456)

This is a framework to formalize and verify Actor systems on Coq.

**There is a possibility to change the repository name**


Requirements
------------

- Coq 8.4pl5


Install
-------

```sh
$ cd /path/to/coq-actor
$ ./configure
$ make
$ make install
```


Examples
--------

See [`examples`](./examples).


Current status
--------------

- [x] Formalization of Actor model's syntax and semantics
    + syntax: `new`, `send`, `self`, `become` (theories/syntax.v, `actions`)
    + semantics: labelled transition semantics (theories/semantics.v, `trans`)
- [x] Convenient notation
    + theories/syntax.v
- [x] Proof of no duplication of Actor names
    + theories/trans_invariant.v (`initial_trans_star_no_dup`)
- [ ] Mechanisms/Lemmas to verify Actor systems
- [ ] Communication between configurations (for distributed systems)
- [ ] Extraction to Erlang
- [ ] Supervisor / Monitor / Link
