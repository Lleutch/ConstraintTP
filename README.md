# ConstraintTP

This project has been inspired from [Dependent Type Provider](https://github.com/caindy/DependentTypesProvider)

It provides compile-time constraints over basic F# types.

The goal would be to allow coders to create types according to specific rules and having value constraint over these rules at compile-time.


## Rule system

The rule system is the following:
We consider that each type could be shrinked down to a subset according to a specific rule.
The rule would be written as a string representation of a function and would return the function itself.
The type of the rule even though it is a **string** should, when evaluated by the fsi Session, be :


        'a -> bool

either the value given follows the rule (_true_) or not (_false_).

For instance, if one wants to define a type with all the integers multiple of 3, he would write :


        let [<Literal>] multiplesOf3Rule = "let f inputValue = inputValue % 3 = 0 \nf"


and would be called as a static parameter of ConstraintTP :


        type DivisibleBy3 = Constraint.Numbers.ConstraintInt32<Rule = multiplesOf3Rule>


## What is supported so far

#### System of rule :

A system of rule that is quite generic and type safe through the pre-évaluation with the fsi session running behind the scene.

#### Basic F# types :

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

#### As a non-basic F# types :

* Arrays

       type: 'a []

> I could do any non-basic F# types like lists... However I think that there are some aspect I should work on before going further.


TODO
***

* String with compile-time Regex verification as follow `Type Foo = DependentType.String.Regex<".+@.+">`


If one has some ideas regarding how we could take this TP to any direction please tell me, I would really appreciate.

## Build process

run the following command :

> .\build.cmd

## Samples

Some basic samples could be found in `Examples.fsx`. You could also look at the [slides](https://lleutch.github.io/FSharpX2017) I have prepared.
