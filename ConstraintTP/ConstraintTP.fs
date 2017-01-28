namespace DependentType

open FSharp.Core.CompilerServices
open Microsoft.FSharp.Quotations
open ProviderImplementation.ProvidedTypes
open System.Reflection 
open System

module SanityCheck =
    type Rules<'a when 'a:comparison> =
        | GreaterThan of 'a
        | LessThan of 'a
        | GreaterEqual of 'a
        | LessEqual of 'a

        member this.Verify(x:'a) =
            match this with
            | GreaterThan y -> x > y
            | LessThan y -> x < y
            | GreaterEqual y -> x >= y
            | LessEqual y -> x <= y

    let checkCoherency greaterThan lessThan greaterEqual lessEqual minValue maxValue negativeInfinity positiveInfinity =
        let gt = greaterThan = negativeInfinity
        let ge = greaterEqual = negativeInfinity
        let lt = lessThan = positiveInfinity
        let le = lessEqual = positiveInfinity
        
        match [gt;ge;lt;le] |> List.filter (id) |> List.length |> ((<>) 0) with
        | true  -> failwith "Unexpected value representing infinity during the rules definition"
        | false -> ()

        
        let ge = greaterEqual = minValue
        let le = lessEqual = maxValue
        
        match [ge;le] |> List.filter (id) |> List.length |> ((=) 2) with
        | true  -> failwith "You have defined a Type that is just a wrapper over an int, create an int instead"
        | false -> ()

        let gt = GreaterThan    greaterThan
        let ge = GreaterEqual   greaterEqual
        let lt = LessThan       lessThan
        let le = LessEqual      lessEqual
        ()


module Rules =
    
    let greaterThan bound value = value > bound
    let lessThan bound value = value < bound
    let equalTo bound value = value = bound
    let greaterOrEqualTo bound value = value >= bound
    let lessOrEqualTo bound value = value <= bound

    let inBounderiesOrEqual boundMin boundMax value = (value |> greaterOrEqualTo boundMin) && (value |> lessOrEqualTo boundMax)
    let inBounderies boundMin boundMax value = (value |> greaterThan boundMin) && (value |> lessThan boundMax)

module private StringDependentType =
    open Rules

    let ns = "DependentType.String"
    let asm = Assembly.GetExecutingAssembly()


    let inline createProvidedType (nameOfTheType:string) (parameters:obj[]) =
        
        let minLength = parameters.[0] :?> int
        let maxLength = parameters.[1] :?> int

        let ty = ProvidedTypeDefinition(asm,ns,nameOfTheType,Some typeof<string>)
        
        let ctor = ProvidedConstructor([ProvidedParameter("Value",typeof<string>)], InvokeCode = (fun args -> args.Head ))
        ctor.SetMethodAttrs(MethodAttributes.PrivateScope)
        ty.AddMember ctor


        let providedProperty =
            ProvidedProperty("RawValue", typeof<string>,IsStatic=false,
                GetterCode = (fun args ->  args.Head ) )
        
        ty.AddMember providedProperty


        let staticParams = [ProvidedStaticParameter("Value", typeof<string>)]
        
        let methodCreate =  
            let staticMethod = ProvidedMethod("Create", [], ty, IsStaticMethod = true)
            staticMethod.DefineStaticParameters(staticParams, (fun name args ->
                let value = args.[0] :?> string
                let length = value.Length
                                
                let invokedMethod = 
                    ProvidedMethod(name, [], ty, IsStaticMethod = true,
                                    InvokeCode = fun args ->
                                        if length |> inBounderiesOrEqual minLength maxLength |> not then
                                            sprintf "The string length : %A should be between %A and %A " length minLength maxLength
                                            |> failwith
                                        Expr.NewObject(ctor,[ <@@ value @@> ])
                                        )
                
                ty.AddMember invokedMethod
                invokedMethod
            ))
            staticMethod
        
        let methodTryCreate =
            let tyType = typedefof<_ option>.MakeGenericType(ty)
            ProvidedMethod("TryCreate", [ProvidedParameter("Value",typeof<string>)], tyType , IsStaticMethod = true,
                            InvokeCode = fun args -> 
                                match args with 
                                | [this] ->
                                    <@@ 
                                        let value = (%%this:string)
                                        let length = value.Length
                                        if length |> inBounderiesOrEqual minLength maxLength |> not then
                                            None
                                        else 
                                            value |> Some                                        
                                    @@>
                                | _ -> failwith "wrong Constructor Argument"

                            )

        ty.AddMember(methodCreate)
        ty.AddMember(methodTryCreate)
        ty.NonNullable <- true
           
        ty

    let inline createTypeString(minLength) =
        let name = "Bounded" + (typeof<string>).Name
        let myType = ProvidedTypeDefinition(asm,ns,name,Some typeof<obj>)
        myType.DefineStaticParameters([ProvidedStaticParameter("MinLength",typeof<int>,minLength);ProvidedStaticParameter("MaxLength",typeof<int>)],createProvidedType)
        myType


module private NumbersDependentType =
    open Rules

    let ns = "DependentType.Numbers"
    let asm = Assembly.GetExecutingAssembly()


    let inline createProvidedType< ^a when ^a:comparison> (nameOfTheType:string) (parameters:obj[]) =
        
        let lowerBound = parameters.[0] :?> ^a
        let upperBound = parameters.[1] :?> ^a

        let ty = ProvidedTypeDefinition(asm,ns,nameOfTheType,Some typeof< ^a>)
 
        let ctor = ProvidedConstructor([ProvidedParameter("Value",typeof< ^a>)],
                                    InvokeCode = (fun args -> args.Head ))
        
        ctor.SetMethodAttrs(MethodAttributes.PrivateScope)
        ty.AddMember ctor
        
        let providedProperty =
            ProvidedProperty("RawValue", typeof< ^a>,IsStatic=false,
                GetterCode = (fun args ->  args.Head ) )
        
        ty.AddMember providedProperty

        let staticParams = [ProvidedStaticParameter("Value", typeof< ^a >)]

        let methodCreate =  
            let staticMethod = ProvidedMethod("Create", [], ty, IsStaticMethod = true)
            staticMethod.DefineStaticParameters(staticParams, (fun name args ->
                let value = args.[0] :?> ^a                
                                                
                let invokedMethod = 
                    ProvidedMethod(name, [], ty, IsStaticMethod = true,
                                    InvokeCode = fun args -> 
                                        if value |> inBounderiesOrEqual lowerBound upperBound |> not then
                                            sprintf "The value: %A should be between %A and %A " value lowerBound upperBound
                                            |> failwith
                                        Expr.NewObject(ctor,[ <@@ value @@> ])
                                  )
                ty.AddMember invokedMethod
                invokedMethod
            ))
            staticMethod
        
                                    
        let methodTryCreate =
            let tyType = typedefof<_ option>.MakeGenericType(ty)
            ProvidedMethod("TryCreate", [ProvidedParameter("Value",typeof< ^a>)], tyType , IsStaticMethod = true,
                            InvokeCode = fun args -> 
                                match args with 
                                | [this] ->
                                    <@@ 
                                        let value = (%%Expr.Coerce(this,typeof< ^a>):'a)
                                        if value |> inBounderiesOrEqual lowerBound upperBound |> not then
                                            None
                                        else 
                                            value |> Some                                        
                                    @@>
                                | _ -> failwith "wrong Constructor Argument"

                            )
            
        ty.AddMember(methodCreate)
        ty.AddMember(methodTryCreate)
        ty.NonNullable <- true
           
        ty

    let inline createType< ^a when ^a : comparison>(minValue: ^a,maxValue: ^a) =
        let name = "Bounded" + (typeof< ^a>).Name
        let myType = ProvidedTypeDefinition(asm,ns,name,Some typeof<obj>)
        let listOfStaticParam =
            [   ProvidedStaticParameter("LowerBound",typeof< ^a >,minValue);
                ProvidedStaticParameter("UpperBound",typeof< ^a >,maxValue)
            ]
        myType.DefineStaticParameters(listOfStaticParam,createProvidedType< ^a>)
        myType



[<TypeProvider>]
type TypeProvider(config : TypeProviderConfig) as this =
    inherit TypeProviderForNamespaces ()

    let numberTypes = [
        NumbersDependentType.createType<byte>(Byte.MinValue,Byte.MaxValue);
        NumbersDependentType.createType<int16>(Int16.MinValue,Int16.MaxValue);
        NumbersDependentType.createType<int32>(Int32.MinValue,Int32.MaxValue);
        NumbersDependentType.createType<int64>(Int64.MinValue,Int64.MaxValue);
        NumbersDependentType.createType<sbyte>(SByte.MinValue,SByte.MaxValue);
        NumbersDependentType.createType<uint16>(UInt16.MinValue,UInt16.MaxValue);
        NumbersDependentType.createType<uint32>(UInt32.MinValue,UInt32.MaxValue);
        NumbersDependentType.createType<uint64>(UInt64.MinValue,UInt64.MaxValue);
        NumbersDependentType.createType<float>(Double.MinValue,Double.MaxValue);
        NumbersDependentType.createType<float32>(Single.MinValue,Single.MaxValue);
    ]

    let stringTypes = [
        StringDependentType.createTypeString(0);
    ]

    do this.AddNamespace(NumbersDependentType.ns,numberTypes)
    do this.AddNamespace(StringDependentType.ns,stringTypes)

[<assembly:TypeProviderAssembly>]
    do()