namespace DependentType

open FSharp.Core.CompilerServices
open Microsoft.FSharp.Compiler.Interactive.Shell
open Microsoft.FSharp.Quotations
open ProviderImplementation.ProvidedTypes

open System
open System.Reflection 
open System.Text
open System.IO


module Fsi =

    // Intialize output and input streams
    let sbOut = new StringBuilder()
    let sbErr = new StringBuilder()
    let inStream = new StringReader("")
    let outStream = new StringWriter(sbOut)
    let errStream = new StringWriter(sbErr)

    // Build command line arguments & start FSI session
    let argv = [| "C:\\fsi.exe" |]
    let allArgs = Array.append argv [|"--noninteractive"|]

    let fsiConfig = FsiEvaluationSession.GetDefaultConfiguration()
    let fsiSession = FsiEvaluationSession.Create(fsiConfig, allArgs, inStream, outStream, errStream) 


module Rules =
    open Fsi

    /// Evaluate expression & return the result, strongly typed
    let evalExpressionRule<'a> (text) = 
        match fsiSession.EvalExpressionNonThrowing(text) with
        |Choice1Of2 fsiValue , errors ->
            if errors.Length = 0 then
                match fsiValue with
                | Some value -> 
                    let f (x:'a) = true
                    let typing = f.GetType().BaseType

                    if (typing = value.ReflectionType) then
                        value.ReflectionValue |> unbox<'a->bool>
                    else
                        let message = 
                            sprintf "Expected a function of type : %A BUT received an element of type %A" typing (value.ReflectionType)
                        failwith message
                | None -> 
                    failwith "The function you have provided doesn't return/do anything!"
            else
                let initialState = (1,"")
                let listedMistakes = 
                    errors
                    |> Array.fold(fun (index,errorListed) error -> 
                        (index + 1, errorListed + "\n" + "Error n°" + (index |> string) + " : " + (error.ErrorNumber |> string ) + " " + error.Message) ) 
                        initialState
                    
                failwith (listedMistakes |> snd)
        |Choice2Of2 exn , errors ->
            let initialState = (1,"")
            let listedMistakes = 
                errors
                |> Array.fold(fun (index,errorListed) error -> 
                    (index + 1, errorListed + "\n" + "Error n°" + (index |> string) + " : " + error.Message) ) 
                    initialState
            let message = (listedMistakes |> snd)
            failwith message


    let evalExpressionArrayOf<'a> (text) = 
        match fsiSession.EvalExpressionNonThrowing(text) with
        |Choice1Of2 fsiValue , errors ->
            if errors.Length = 0 then
                match fsiValue with
                | Some value -> 
                    let fArray () : 'a [] = [||]
                    let array = fArray()
                    let typing = typeof<'a []>
                    if (typing = value.ReflectionType) then
                        value.ReflectionValue |> unbox<'a []>
                    else
                        let message = 
                            sprintf "Expected an Array of type : %A BUT received an element of type %A" typing (value.ReflectionType)
                        failwith message
                | None -> 
                    failwith "The array you have provided is incorrect"
            else
                let initialState = (1,"")
                let listedMistakes = 
                    errors
                    |> Array.fold(fun (index,errorListed) error -> 
                        (index + 1, errorListed + "\n" + "Error n°" + (index |> string) + " : " + (error.ErrorNumber |> string ) + " " + error.Message) ) 
                        initialState
                    
                failwith (listedMistakes |> snd)
        |Choice2Of2 exn , errors ->
            let initialState = (1,"")
            let listedMistakes = 
                errors
                |> Array.fold(fun (index,errorListed) error -> 
                    (index + 1, errorListed + "\n" + "Error n°" + (index |> string) + " : " + error.Message) ) 
                    initialState
            let message = (listedMistakes |> snd)
            failwith message









module private StringConstraintType =
    open Rules

    let ns = "Constraint.String"
    let asm = Assembly.GetExecutingAssembly()


    let inline createProvidedType (nameOfTheType:string) (parameters:obj[]) =
        
        // Getting the first parameter representing the rule to follow for this specific type (string)
        let stringlyTypedRule = parameters.[0] :?> string
        let typing = typeof<string>
        // The evaluated function
        let _ = evalExpressionRule<string> (stringlyTypedRule)
        
        // The provided Type
        let ty = ProvidedTypeDefinition(asm,ns,nameOfTheType,Some typeof<string>)
        ty.HideObjectMethods <- true
        
        // The associated Constructor which creates an object of type : Provided Type
        let ctor = ProvidedConstructor([ProvidedParameter("Value",typing)], InvokeCode = (fun args -> args.Head ))
        ctor.SetMethodAttrs(MethodAttributes.PrivateScope)
        ty.AddMember ctor

        // Property to get the RawValue : to it's basic type
        let providedProperty =
            ProvidedProperty("RawValue", typing,IsStatic=false,
                GetterCode = (fun args ->  args.Head ) )
        ty.AddMember providedProperty


        // Static method that creates at run time the Provided Type value, But verifies the rules at compile-time
        let methodCreate =  
            let staticParams = [ProvidedStaticParameter("Value", typing)]
            let staticMethod = ProvidedMethod("Create", [], ty, IsStaticMethod = true)
            staticMethod.DefineStaticParameters(staticParams, (fun name args ->
                
                // The value given by the user as a static parameters
                let value = args.[0] :?> string
                let evaluatedFunction = evalExpressionRule<string> (stringlyTypedRule)                                
                
                let invokedMethod = 
                    ProvidedMethod(name, [], ty, IsStaticMethod = true,
                                    InvokeCode = fun args ->
                                        let result = evaluatedFunction(value)
                                        if not result then
                                            "The value given doesn't follow the rule you have provided to this type"
                                            |> failwith
                                        Expr.NewObject(ctor,[ <@@ value @@> ])
                                        )
                
                ty.AddMember invokedMethod
                invokedMethod
            ))
            staticMethod
        
        // Method that can only verify the rule at run-time. This is when the parameter cannot be static (not a literal)
        let methodTryCreate =
            let tyType = typedefof<_ option>.MakeGenericType(ty)
            ProvidedMethod("TryCreate", [ProvidedParameter("Value",typing)], tyType , IsStaticMethod = true,
                            InvokeCode = fun args -> 
                                match args with 
                                | [this] ->
                                    <@@ 
                                        let value = (%%this:string)
                                        
                                        let evaluatedFunction = evalExpressionRule<string> (stringlyTypedRule)
                                        let result = evaluatedFunction(value)
                                        if not result then
                                            None
                                        else
                                            Some value
                                    @@>
                                | _ -> failwith "wrong Constructor Argument"

                            )

        ty.AddMember(methodCreate)
        ty.AddMember(methodTryCreate)
        ty.NonNullable <- true
           
        ty

    let inline createTypeString() =
        let name = "Constraint" + (typeof<string>).Name
        let myType = ProvidedTypeDefinition(asm,ns,name,Some typeof<obj>)
        let listOfStaticParam =
            [   ProvidedStaticParameter("Rule",typeof<string>)
            ]
        myType.DefineStaticParameters(listOfStaticParam,createProvidedType)
        myType

module private NumbersConstraintType =
    open Rules

    let ns = "Constraint.Numbers"
    let asm = Assembly.GetExecutingAssembly()


    let inline createProvidedType< ^a when ^a:comparison> (nameOfTheType:string) (parameters:obj[]) =
        
        // Getting the first parameter representing the rule to follow for this specific type (string)
        let stringlyTypedRule = parameters.[0] :?> string
        let typing = typeof< ^a>
        
        // The evaluated function
        let _ = evalExpressionRule< ^a> (stringlyTypedRule)

        // The provided Type
        let ty = ProvidedTypeDefinition(asm,ns,nameOfTheType,Some typeof< ^a>)
        ty.HideObjectMethods <- true

        // The associated Constructor which creates an object of type : Provided Type 
        let ctor = ProvidedConstructor([ProvidedParameter("Value",typing)],
                                    InvokeCode = (fun args -> args.Head ))        
        ctor.SetMethodAttrs(MethodAttributes.PrivateScope)
        ty.AddMember ctor
        
        // Property to get the RawValue : to it's basic type
        let providedProperty =
            ProvidedProperty("RawValue", typing ,IsStatic=false,
                GetterCode = (fun args ->  args.Head ) )
        ty.AddMember providedProperty

        
        // Static method that creates at run time the Provided Type value, But verifies the rules at compile-time
        let methodCreate =  
            let staticParams = [ProvidedStaticParameter("Value", typing)]
            let staticMethod = ProvidedMethod("Create", [], ty, IsStaticMethod = true)
            staticMethod.DefineStaticParameters(staticParams, (fun name args ->

                // The value given by the user as a static parameters
                let value = args.[0] :?> ^a            
                // The evaluated function
                let evaluatedFunction = evalExpressionRule< ^a> (stringlyTypedRule)
    
                                                
                let invokedMethod = 
                    ProvidedMethod(name, [], ty, IsStaticMethod = true,
                                    InvokeCode = fun args -> 
                                        let result = evaluatedFunction(value)
                                        if not result then
                                            "The value given doesn't follow the rule you have provided to this type"
                                            |> failwith
                                        Expr.NewObject(ctor,[ <@@ value @@> ])
                                  )
                ty.AddMember invokedMethod
                invokedMethod
            ))

            staticMethod
        
        // Method that can only verify the rule at run-time. This is when the parameter cannot be static (not a literal)                                    
        let methodTryCreate =
            let tyType = typedefof<_ option>.MakeGenericType(ty)
            
            ProvidedMethod("TryCreate", [ProvidedParameter("Value",typing)], tyType , IsStaticMethod = true,
                            InvokeCode = fun args -> 
                                match args with 
                                | [this] ->
                                    <@@ 
                                        let realValue = (%%Expr.Coerce(this,typing):'a)
                                        
                                        // The evaluated function
                                        let evaluatedFunction = evalExpressionRule< ^a> (stringlyTypedRule)

                                        let result = evaluatedFunction(realValue )
                                        if not result then
                                            None
                                        else
                                            Some realValue
                                    @@>
                                | _ -> failwith "wrong Constructor Argument"

                            )
            
        ty.AddMember(methodCreate)
        ty.AddMember(methodTryCreate)
        ty.NonNullable <- true
           
        ty

    let inline createType< ^a when ^a : comparison>() =
        let name = "Constraint" + (typeof< ^a>).Name
        let myType = ProvidedTypeDefinition(asm,ns,name,Some typeof<obj>)
        let listOfStaticParam =
            [   ProvidedStaticParameter("Rule",typeof<string>)
            ]
        myType.DefineStaticParameters(listOfStaticParam,createProvidedType< ^a>)
        myType



module private ArrayConstraintType =
    open Rules

    let ns = "Constraint.ArrayOfNumber"
    let asm = Assembly.GetExecutingAssembly()


    let inline createProvidedType< ^a when ^a:comparison> (nameOfTheType:string) (parameters:obj[]) =
        
        // Getting the first parameter representing the rule to follow for this specific type (string)
        let stringlyTypedRule = parameters.[0] :?> string
        let typing = typeof< ^a []>
        // The evaluated function
        let _ = evalExpressionRule< ^a []> (stringlyTypedRule)


        // The provided Type
        let ty = ProvidedTypeDefinition(asm,ns,nameOfTheType,Some typeof< ^a []>)
        ty.HideObjectMethods <- true

        // The associated Constructor which creates an object of type : Provided Type 
        let ctor = ProvidedConstructor([ProvidedParameter("Value",typing)],
                                    InvokeCode = (fun args -> args.Head ))        
        ctor.SetMethodAttrs(MethodAttributes.PrivateScope)
        ty.AddMember ctor
        
        // Property to get the RawValue : to it's basic type
        let providedProperty =
            ProvidedProperty("RawValue", typing ,IsStatic=false,
                GetterCode = (fun args ->  args.Head ) )
        ty.AddMember providedProperty

        // Static method that creates at run time the Provided Type value, But verifies the rules at compile-time
        let methodCreate =  
            let staticParams = [ProvidedStaticParameter("Value", typeof<string>)]
            let staticMethod = ProvidedMethod("Create", [], ty, IsStaticMethod = true)
            staticMethod.DefineStaticParameters(staticParams, (fun name args ->

                // The value given by the user as a static parameters
                let value = args.[0] :?> string
                let evaluatedArray = evalExpressionArrayOf< ^a> (value)
                // The evaluated function
                let evaluatedFunction = evalExpressionRule< ^a []> (stringlyTypedRule)

                                                
                let invokedMethod = 
                    ProvidedMethod(name, [], ty, IsStaticMethod = true,
                                    InvokeCode = fun args -> 
                                        let result = evaluatedFunction(evaluatedArray)
                                        if not result then
                                            "The value given doesn't follow the rule you have provided to this type"
                                            |> failwith
                                        Expr.NewObject(ctor,[ <@@ evaluatedArray @@> ])
                                  )
                ty.AddMember invokedMethod
                invokedMethod
            ))

            staticMethod
        
        // Method that can only verify the rule at run-time. This is when the parameter cannot be static (not a literal)                                    
        let methodTryCreate =
            let tyType = typedefof<_ option>.MakeGenericType(ty)
            ProvidedMethod("TryCreate", [ProvidedParameter("Value",typeof<string>)], tyType , IsStaticMethod = true,
                            InvokeCode = fun args -> 
                                match args with 
                                | [this] ->
                                    <@@ 
                                        let evaluatedFunction = evalExpressionRule< ^a []> (stringlyTypedRule)

                                        let value = (%%this:string)
                                        let evaluatedArray = evalExpressionArrayOf< ^a> (value)
                                        let result = evaluatedFunction(evaluatedArray)

                                        if not result then
                                            None
                                        else
                                            Some evaluatedArray                                      
                                    @@>
                                | _ -> failwith "wrong Constructor Argument"

                            )
            
        ty.AddMember(methodCreate)
        ty.AddMember(methodTryCreate)
        ty.NonNullable <- true
           
        ty

    let inline createType< ^a when ^a : comparison>() =
        let name = "Constraint" + (typeof< ^a>).Name + "Array"
        let myType = ProvidedTypeDefinition(asm,ns,name,Some typeof<obj>)
        let listOfStaticParam =
            [   ProvidedStaticParameter("Rule",typeof<string>)
            ]
        myType.DefineStaticParameters(listOfStaticParam,createProvidedType< ^a>)
        myType


[<TypeProvider>]
type TypeProvider(config : TypeProviderConfig) as this =
    inherit TypeProviderForNamespaces ()


//    let ruleByte    = "let f (x:byte) = true \nf"
//    let ruleInt16   = "let f (x:int16) = true \nf"
//    let ruleInt32   = "let f (x:int32) = true \nf"
//    let ruleInt64   = "let f (x:int64) = true \nf"
//    let ruleSByte   = "let f (x:sbyte) = true \nf"
//    let ruleUInt16  = "let f (x:uint16) = true \nf"
//    let ruleUInt32  = "let f (x:uint32) = true \nf"
//    let ruleUInt64  = "let f (x:uint64) = true \nf"
//    let ruleFloat   = "let f (x:float) = true \nf"
//    let ruleFloat32 = "let f (x:float32) = true \nf"

    let numberTypes = [
        NumbersConstraintType.createType<byte>();
        NumbersConstraintType.createType<int16>();
        NumbersConstraintType.createType<int32>();
        NumbersConstraintType.createType<int64>();
        NumbersConstraintType.createType<sbyte>();
        NumbersConstraintType.createType<uint16>();
        NumbersConstraintType.createType<uint32>();
        NumbersConstraintType.createType<uint64>();
        NumbersConstraintType.createType<float>();
        NumbersConstraintType.createType<float32>();
    ]


//    let ruleString =
//        "let f (x:string) = true \nf"

    let stringTypes = [
        StringConstraintType.createTypeString();
    ]

//    let ruleByteArray       = "let f (x:byte []) = true \nf"
//    let ruleInt16Array      = "let f (x:int16 []) = true \nf"
//    let ruleInt32Array      = "let f (x:int32 []) = true \nf"
//    let ruleInt64Array      = "let f (x:int64 []) = true \nf"
//    let ruleSByteArray      = "let f (x:sbyte []) = true \nf"
//    let ruleUInt16Array     = "let f (x:uint16 []) = true \nf"
//    let ruleUInt32Array     = "let f (x:uint32 []) = true \nf"
//    let ruleUInt64Array     = "let f (x:uint64 []) = true \nf"
//    let ruleFloatArray      = "let f (x:float []) = true \nf"
//    let ruleFloat32Array    = "let f (x:float32 []) = true \nf"

    let numberArrayTypes = [
        ArrayConstraintType.createType<byte>();
        ArrayConstraintType.createType<int16>();
        ArrayConstraintType.createType<int32>();
        ArrayConstraintType.createType<int64>();
        ArrayConstraintType.createType<sbyte>();
        ArrayConstraintType.createType<uint16>();
        ArrayConstraintType.createType<uint32>();
        ArrayConstraintType.createType<uint64>();
        ArrayConstraintType.createType<float>();
        ArrayConstraintType.createType<float32>();
    ]



    do this.AddNamespace(NumbersConstraintType.ns,numberTypes)
    do this.AddNamespace(StringConstraintType.ns,stringTypes)
    do this.AddNamespace(ArrayConstraintType.ns,numberArrayTypes)

[<assembly:TypeProviderAssembly>]
    do()