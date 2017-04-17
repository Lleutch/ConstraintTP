#r "bin/Debug/ConstraintTP.dll"

// 1) Probability
let [<Literal>] probaRule = "let f (x:float) = x>=0. && x<= 1. \nf"

type Probability = Constraint.Numbers.ConstraintDouble<Rule = probaRule>

let aProba = Probability.Create<0.5>()
let notProba = Probability.Create<0.6>()
let someProba = Probability.TryCreate(0.2)


// 2) division by 3 if divisible by 3
// 2/3 -> X 
// 3/3 -> v

let [<Literal>] divisibleBy3Rule = "let f x = x % 3 = 0 \nf"
type DivisibleBy3 = Constraint.Numbers.ConstraintInt32<Rule = divisibleBy3Rule>

let divideBy3 (x:DivisibleBy3) =
    x.RawValue/3

let rand = System.Random()
let x = rand.Next()

let div3 = DivisibleBy3.TryCreate(x)

match div3 with
|None -> printfn "None"
|Some elem -> 
    let res = divideBy3 elem
    printfn "%d" res



// 3) zip Arrays size 3
let [<LiteralAttribute>] zipRuleBytes = "let f (x: byte []) = x.Length = 3 \nf"
let propertyToCheckOnInstance = "x.Length"
let propertyToCheckOnTypeAndModule = "Array.Length"
let genericValueOnProperty = "n"

type zipArrayBytes = Constraint.ArrayOfNumber.ConstraintByteArray<zipRuleBytes>


type ZipArr<'n> =
    | Array of 'n 
    | Or

let [<LiteralAttribute>] zipRuleInts = "let f (x: int []) = x.Length = 4 \nf"
type zipArrayInts = Constraint.ArrayOfNumber.ConstraintInt32Array<zipRuleInts>

let [<Literal>] arrayByte = "[|0uy;1uy;2uy|]"
let [<Literal>] arrayInt = "[|3;4;5;6|]"

let arrayByteConstraint = zipArrayBytes.Create<arrayByte>()
let arrayIntConstraint = zipArrayInts.Create<arrayInt>()

let zipSize3 (arrayByte:zipArrayBytes) (arrayInt:zipArrayInts) =
    let byteArray = arrayByte.RawValue
    let intArray = arrayInt.RawValue
    Array.zip byteArray intArray


let result = zipSize3 arrayByteConstraint arrayIntConstraint
