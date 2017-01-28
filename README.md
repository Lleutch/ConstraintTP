# ConstraintTP

This project has been inspired from [Dependent Type Provider](https://github.com/caindy/DependentTypesProvider)

It provides compile-time constraints over basic F# types.

The goal would be to allow coders to create types according to specific rules and having value constraint over these rules at compile-time.


For the moment, just a few types are covered:

* sbyte
* byte
* uint16
* int16
* uint32
* int32
* uint64
* int64
* float32
* float


TODO

***

* String with compile-time Regex verification as follow `Type Foo = DependentType.String.Regex<".+@.+">`
* Static parameter = rules to be parsed using FCS instead of lowerBound and upperBound