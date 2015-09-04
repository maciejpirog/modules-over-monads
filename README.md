Modules over Monads library
===========================

Haskell library for modules over monads, idealised monads, and ideal monads. See, for example, S.Milius [Completely iterative algebras and completely iterative monads](http://www.iti.cs.tu-bs.de/~milius/phd/M1.pdf) for the abstract nonsense.

Files
-----

Note that the current placement of things in files is rather temporary. At the moment:

* **Module.hs** basic typeclasses
* **Instances.hs** instances of the basic typeclasses and datatypes used to represent the appropriate modules
* **IdealCoproduct.hs** coproduct of ideal monads (see N.Ghani, T.Uustalu [Coproducts of ideal monads](http://www.cs.ioc.ee/~tarmo/papers/fics03-tia.pdf))
* **Resumption.hs** generalised resumption monad (see M.Piróg, N.Wu, J.Gibbons [Modules over monads and their algebras](https://coalg.org/calco15/papers/p18-Pir%C3%B3g.pdf))
* **MonoidIDeal.hs** ideal monoids, that is, monoids that are semigroups with freely adjoined unit

Run `make` to compile haddock docs.

Dependencies
------------

* `void`
* `mtl`
* `semigroups`
* `free`
