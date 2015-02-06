Actario - Verification Framework for Actor Systems on Coq
=========================================================

[![wercker status](https://app.wercker.com/status/1f0b20fd4377f1065457f7b480919621/m "wercker status")](https://app.wercker.com/project/bykey/1f0b20fd4377f1065457f7b480919621)

Actario is a framework to formalize and verify Actor systems on Coq. **highly development**

Actario = Actor + Scenario


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
- [ ] Communication between configurations
- [x] Extraction to Erlang
    + Equivalence between Actario's semantics and Erlang's semantics is not proven
- [ ] Supervisor
- [ ] Practical examples


License
-------

LGPL 2.1
