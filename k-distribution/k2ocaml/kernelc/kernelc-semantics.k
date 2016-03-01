// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module KERNELC-SEMANTICS
  imports KERNELC-SYNTAX

  /*
   * Macros
   */
  rule return; => return tv(void, undef);                   [macro]
  rule NULL => tv(void *, null)                             [macro]

  /* block without declarations macro (for use in the semantics only) */
  syntax Block ::= "{" Statements "}"
  rule { Ss:Statements } => { .VariableDeclarations Ss }    [macro]


  /*
   * Typed values
   */
  syntax Expression ::= EvaluatedExpression
  syntax EvaluatedExpression ::= TypedValue
                               | Bool
                               | String
  syntax EvaluatedExpressions ::= List{EvaluatedExpression, ","}

  syntax TypedValue ::= "tv" "(" Type "," Value ")"
  syntax Value ::= Int
                 | Float
                 | Pointer
                 | "undef"
  syntax Pointer ::= "object" "(" Int ")"           [smtlib(smt_pointer_object)]
                   | "member" "(" Int "," Id ")"
                   | "null"                         [smtlib(smt_pointer_null)]


  /*
   * Process global definitions and declarations one at a time
   */
  rule G:Global Gs:Globals => G ~> Gs   [structural]
  rule .Globals => .K                   [structural]


  /*
   * Elide #include directives
   */
  rule #include<stdlib.h> => .K   [structural]
  rule #include<stdio.h>  => .K   [structural]


  /*
   * Definitions/declarations
   */
  /* Function definition */
  syntax KItem ::= functionBody(ParameterDeclarations, Type, Block)
  rule
    <k> T:Type F:Id(PDs:ParameterDeclarations) B:Block => .K ...</k>
    //<fun>... .Map => F |-> functionBody(PDs, T, { B return; }) ...</fun>
    <fun>... .Map => F |-> functionBody(PDs, T, B) ...</fun>
    [structural]
  /* Elide function declarations */
  rule T:Type F:Id(PDs:ParameterDeclarations); => .K   [structural]

  /* Structure declaration */
  rule
    <k> struct S:Id { VDs:VariableDeclarations }; => .K ...</k>
    <struct>... .Map => S |-> makeMemberMap(VDs) ...</struct>
    [structural]

  /* Variable declaration */
  rule VD:VariableDeclaration VDs:VariableDeclarations => VD ~> VDs
    [structural]
  rule .VariableDeclarations => .K    [structural]
  rule
    <k> T:Type X:Id; => .K ...</k>
    <env> Env:Map => Env[X <- tv(T *, object(!I:Int))] </env>
    <stackMemory>... .Map => object(!I) |-> tv(T, undef) ...</stackMemory>
    <locals>... .List => ListItem(tv(T *, object(!I:Int))) </locals>
    [structural]


  /*
   * Structural statements
   */
  rule S1:Statement S2:Statement Ss:Statements => S1 ~> S2 Ss   [structural]
  rule S:Statement .Statements => S                             [structural]
  rule .Statements => .K                                        [structural]


  /*
   * Sequence point
   */
  //rule _:TypedValue; => .K    [structural]
  rule ; => .K                [structural]


  /*
   * Block statement
   */
  rule
    <k>
      { VDs:VariableDeclarations Ss:Statements } => VDs ~> Ss ~> Env ~> Locals
    ...</k>
    <env> Env:Map </env>
    <locals> Locals:List => .List </locals>
    requires VDs =/=K .VariableDeclarations
    [structural]
  rule { .VariableDeclarations Ss:Statements } => Ss    [structural]
  rule
    <k> Env:Map ~> Locals:List => deleteLocals(BlockLocals) ...</k>
    <env> _:Map => Env </env>
    <locals> BlockLocals:List => Locals </locals>
    [structural]

  syntax KItem ::= deleteLocals(List)
  rule
    <k> deleteLocals((ListItem(tv(_:Type, P:Pointer)) => .List) L:List) ...</k>
    <stackMemory>... P |-> _ => .Map...</stackMemory>
    [structural]
  rule deleteLocals(.List) => .K    [structural]


  /*
   * If/choice
   */
  //rule if (E:Expression) S1:Statement else S2:Statement
  //  => expression2bool(E) ~> if (HOLE) S1 else S2
  //  [heat]
  //rule B:Bool ~> if (HOLE) S1:Statement else S2:Statement
  //  => if (B) S1 else S2
  //  [cool]
  //rule if( true) S:Statement else _:Statement => S    [structural]
  //rule if(false) _:Statement else S:Statement => S    [structural]

  //rule E1:Expression ? E2:Expression : E3:Expression
  //  => expression2bool(E1) ~> HOLE ? E2 : E3
  //  [heat]
  //rule B:Bool ~> HOLE ? E1:Expression : E2:Expression
  //  => B ? E1 : E2
  //  [cool]
  //rule  true ? E:Expression : _:Expression => E   [structural]
  //rule false ? _:Expression : E:Expression => E   [structural]

  syntax KItem ::= "expression2bool" "(" Expression ")"           [strict]
  rule expression2bool(tv(int, I:Int)) => I =/=K 0                [structural]
  rule expression2bool(tv(T:Type *, P:Pointer)) => P =/=K null    [structural]


  /*
   * while
   */
  //rule while (E:Expression) S:Statement => if (E) { S while(E) S }
  //  [structural]


  /*
   * Function call/return
   */
  //syntax KItem ::= callStackFrame(K, Map, List, Id)
  //rule
  //  <fun>...
  //    Callee |-> functionBody(PDs:ParameterDeclarations, _:Type, B:Block)
  //  ...</fun>
  //  <k>
  //    Callee:Id(EEs:EvaluatedExpressions) ~> K
  //  =>
  //    { declareParameters(PDs) bindParameters(PDs, EEs, B) }
  //  </k>
  //  <stack>
  //    .List => ListItem(callStackFrame(K, Env, Locals, Caller))
  //  ...</stack>
  //  <fun-id> Caller:Id => Callee </fun-id>
  //  <env> Env:Map => .Map </env>
  //  <locals> Locals:List => .List </locals>
  //  // TODO: handle special function more generically
  //  requires Callee =/=K malloc andBool Callee =/=K free
  //   andBool Callee =/=K scanf andBool Callee =/=K printf
  //rule
  //  <fun>...
  //    Callee |-> functionBody(_:ParameterDeclarations, T, _:Block)
  //  ...</fun>
  //  <k>
  //    return tv(T:Type, V:Value); ~> _
  //  =>
  //    deleteLocals(values(CalleeEnv)) ~> tv(T, V) ~> K
  //  </k>
  //  <stack>
  //    ListItem(callStackFrame(K, CallerEnv:Map, CallerLocals:List, Caller:Id))
  //  =>
  //    .List
  //  ...</stack>
  //  <fun-id> Callee:Id => Caller </fun-id>
  //  <env> CalleeEnv:Map => CallerEnv </env>
  //  <locals> _:List => CallerLocals </locals>


  /*
   * Memory operations
   */
  rule X:Id => *&X                      [structural]
  rule E:Expression->F:Id => *&(E->F)   [structural]
  rule &*E:Expression => E              [structural]

  /* memory address computation */
  rule
    <k> &X:Id => TV ...</k>
    <env>... X |-> TV:TypedValue ...</env>
    [structural]
  context &(HOLE->_)
  rule
    <k>
      &(tv(struct S:Id *, object(I:Int))->F:Id)
    =>
      tv(T *, member(I, F))
    ...</k>
    <struct>... S |-> (F |-> T:Type _:Map) ...</struct>
    [structural]

  /* memory read */
  rule
    <k> *tv(T:Type *, object(I:Int)) => tv(T, V) ...</k>
    <stackMemory>... object(I) |-> tv(T, V:Value) ...</stackMemory>
    requires V =/=K undef
    [transition]
  rule
    <k> *tv(T:Type *, member(I:Int, F:Id)) => tv(T, V) ...</k>
    <heapMemory>... object(I) |-> (F |-> tv(T, V:Value) _:Map) ...</heapMemory>
    requires V =/=K undef
    [transition]

  /* memory write */
  rule E1:Expression = E2:EvaluatedExpression; => &E1 ~> HOLE = E2;   [heat]
  rule TV:TypedValue ~> HOLE = E:EvaluatedExpression; => TV = E;      [cool]
  rule
    <k> tv(T:Type *, object(I:Int)) = tv(T, V:Value); => .K ...</k>
    <stackMemory>... object(I) |-> tv(T, _:Value => V) ...</stackMemory>
    requires V =/=K undef
    [transition]
  rule
    <k> tv(T:Type *, member(I:Int, F:Id)) = tv(T, V:Value); => .K ...</k>
    <heapMemory>... object(I) |-> (F |-> tv(T, _:Value => V) _:Map) ...</heapMemory>
    requires V =/=K undef
    [transition]

  /*
   * Boolean and arithmetic operations
   */
  rule I:Int => tv(int, I)                    [structural]
  // TODO: node unary -Int?
  rule -tv(int, I:Int) => tv(int, 0 -Int I)   [structural]
  rule ~tv(int, I:Int) => tv(int, ~Int I)     [structural]
  rule
    tv(int, I1:Int) + tv(int, I2:Int) => tv(int, I1 +Int I2)
    [structural]
  rule
    tv(int, I1:Int) - tv(int, I2:Int) => tv(int, I1 -Int I2)
    [structural]
  rule
    tv(int, I1:Int) * tv(int, I2:Int) => tv(int, I1 *Int I2)
    [structural]
  rule
    tv(int, I1:Int) / tv(int, I2:Int) => tv(int, I1 /Int I2)
    requires I2 =/=K 0
    [structural]
  rule
    tv(int, I1:Int) % tv(int, I2:Int) => tv(int, I1 %Int I2)
    requires I2 =/=K 0
    [structural]
  rule
    tv(int, I1:Int) << tv(int, I2:Int) => tv(int, I1 <<Int I2)
    [structural]
  rule
    tv(int, I1:Int) >> tv(int, I2:Int) => tv(int, I1 >>Int I2)
    [structural]
  rule
    tv(int, I1:Int) >= tv(int, I2:Int) => bool2int(I1 >=Int I2)
    [structural]
  rule
    tv(int, I1:Int) >  tv(int, I2:Int) => bool2int(I1 >Int  I2)
    [structural]
  rule
    tv(int, I1:Int) <= tv(int, I2:Int) => bool2int(I1 <=Int I2)
    [structural]
  rule
    tv(int, I1:Int) <  tv(int, I2:Int) => bool2int(I1 <Int  I2)
    [structural]

  rule F:Float => tv(double, F)                         [structural]
  rule -tv(double, F:Float) => tv(double, --Float F)    [structural]
  rule
    tv(double, F1:Float) + tv(double, F2:Float) => tv(double, F1 +Float F2)
    [structural]
  rule
    tv(double, F1:Float) - tv(double, F2:Float) => tv(double, F1 -Float F2)
    [structural]
  rule
    tv(double, F1:Float) * tv(double, F2:Float) => tv(double, F1 *Float F2)
    [structural]
  rule
    tv(double, F1:Float) / tv(double, F2:Float) => tv(double, F1 /Float F2)
    [structural]
  rule
    tv(double, F1:Float) % tv(double, F2:Float) => tv(double, F1 %Float F2)
    [structural]
  rule
    tv(double, F1:Float) ^ tv(double, F2:Float) => tv(double, F1 ^Float F2)
    [structural]
  rule
    tv(double, F1:Float) >= tv(double, F2:Float) => bool2int(F1 >=Float F2)
    [structural]
  rule
    tv(double, F1:Float) > tv(double, F2:Float) => bool2int(F1 >Float F2)
    [structural]
  rule
    tv(double, F1:Float) <= tv(double, F2:Float) => bool2int(F1 <=Float F2)
    [structural]
  rule
    tv(double, F1:Float) < tv(double, F2:Float) => bool2int(F1 <Float F2)
    [structural]

  rule
    tv(T:Type, V1:Value) == tv(T, V2:Value) => bool2int(V1 ==K  V2)
    [structural]
  rule
    tv(T:Type, V1:Value) != tv(T, V2:Value) => bool2int(V1 =/=K V2)
    [structural]

  syntax KItem ::= "bool2int" "(" Bool ")"    [function]
  rule bool2int(B:Bool) => tv(int, ite(B, 1, 0))
//  syntax KItem ::= "bool2int" "(" Bool ")"
//  rule bool2int( true) => tv(int, 1)    [structural]
//  rule bool2int(false) => tv(int, 0)    [structural]


  /*
   * Cast
   */
  // TODO: cast is disabled for now
  //rule (T) tv(_, V) => tv(T, V) [structural]


  /*
   * Pointer conversions
   */
  rule tv(T1:Type **, _:Pointer) = tv((T2:Type * => T1 *), null);
    requires T1 =/=K T2
    [structural]
  rule tv(T1:Type *, _:Pointer) == tv((T2:Type * => T1 *), null)
    requires T1 =/=K T2
    [structural]
  rule tv((T1:Type * => T2 *), null) == tv(T2:Type *, _:Pointer)
    requires T1 =/=K T2
    [structural]
  rule tv(T1:Type *, _:Pointer) != tv((T2:Type * => T1 *), null)
    requires T1 =/=K T2
    [structural]
  rule tv((T1:Type * => T2 *), null) != tv(T2:Type *, _:Pointer)
    requires T1 =/=K T2
    [structural]
  rule
    <fun>...
      Callee |-> functionBody(_:ParameterDeclarations, T2:Type *, _:Block)
    ...</fun>
    <k> return tv((T1:Type * => T2 *), null); ...</k>
    <fun-id> Callee:Id </fun-id>
    [structural]


  /*
   * Sizeof
   */
  rule sizeof(int) => tv(int, 1)        [structural]
  rule sizeof(double) => tv(int, 1)     [structural]
  rule sizeof(T:Type *) => tv(int, 1)   [structural]
  rule
    <k> sizeof(struct S:Id) => tv(int, size(Members)) ...</k>
    <struct>... S |-> Members:Map ...</struct>
    [structural]


  /*
   * Memory management
   */
  /* malloc only allocates one structure */
  // TODO: check why the HOLE below does not become a freezer
  rule
    <k>
      malloc(tv(int, Size:Int)) ~> (struct S:Id *) HOLE:>Expression
    =>
      tv(struct S *, object(!I:Int))
    ...</k>
    <heapMemory>... .Map => object(!I) |-> initializeObject(Members) ...</heapMemory>
    <struct>... S |-> Members:Map ...</struct>
    when Size ==K size(Members)
    [structural]
  syntax TypedValue ::= makeNewObject(Int)
  rule malloc(tv(int, Size:Int)) => makeNewObject(Size)
  rule
    <k>
      (struct S:Id *) makeNewObject(Size)
    =>
      tv(struct S *, object(!I:Int))
    ...</k>
    <heapMemory>... .Map => object(!I) |-> initializeObject(Members) ...</heapMemory>
    <struct>... S |-> Members:Map ...</struct>
    when Size ==K size(Members)
    [structural]
  rule
    <k> free(tv(T:Type *, object(I:Int))) => tv(void, undef) ...</k>
    <heapMemory>... object(I) |-> _ => .Map ...</heapMemory>


  /*
   * I/O
   */
  //rule
  //  <k>
  //    scanf(_:String, tv(int *, P:Pointer))
  //  =>
  //    tv(int *, P) = tv(int, I); ~> tv(void, undef)
  //  ...</k>
  //  <in> ListItem(I:Int) => .List ...</in>
  //  [structural]
  //rule
  //  <k> printf(_:String, tv(int, I:Int)) => tv(void, undef) ...</k>
  //  <out>... .List => ListItem(I) </out>
  //  [structural]
  //rule printf(_:String) => tv(void, undef)   [structural]


  /*
   * Helper functions
   */
  syntax Map ::= initializeObject(Map)    [function]
  rule initializeObject(F:Id |-> T:Type M:Map)
    => F |-> tv(T, undef) initializeObject(M)
  rule initializeObject(.Map) => .Map

  syntax Map ::= makeMemberMap(VariableDeclarations)    [function]
  rule makeMemberMap(T:Type X:Id; VDs:VariableDeclarations)
    => X |-> T makeMemberMap(VDs)
  rule makeMemberMap(.VariableDeclarations) => .Map

  syntax VariableDeclarations ::= declareParameters(ParameterDeclarations)
    [function]
  rule declareParameters(T:Type X:Id, PDs:ParameterDeclarations)
    => T X; declareParameters(PDs)
  rule declareParameters(.ParameterDeclarations) => .VariableDeclarations

  syntax Statements ::=
    bindParameters(ParameterDeclarations, EvaluatedExpressions, Block)
    [function]
  rule bindParameters(
          (_:Type X:Id, PDs:ParameterDeclarations),
          (TV:TypedValue, EEs:EvaluatedExpressions),
          B:Block)
    => X = TV; bindParameters(PDs, EEs, B)
  rule bindParameters(.ParameterDeclarations, .EvaluatedExpressions, B:Block)
    => B .Statements


  //----------------------------------------------------------------------------
  syntax KItem ::= extendedBlock(K)
                 | "beginExtendedBlock"
                 | "endExtendedBlock"
                 | "beginBasicBlock"
                 | "endBasicBlock"
  syntax KItem ::= addCode(String)
                 | addString(String)
  syntax KItem ::= "#initialize" "(" String "," String ")"            [function, impure, hook(Gen.init)]
  syntax String ::= "#generate" "(" Map "," Map "," List "," K ")"    [function, impure, hook(Gen.gen)]
                  | "#name" "(" K ")"                                 [function, impure, hook(Gen.name)]

  rule extendedBlock(K)
    => beginExtendedBlock
       ~> beginBasicBlock
       ~> K
       ~> endBasicBlock
       ~> endExtendedBlock
    [macro]
  rule
    <k> beginExtendedBlock => .K ...</k>
    <code> C:String => "" </code>
    <codeStack>... .List => ListItem(C) </codeStack>
  rule
    <k> endExtendedBlock => C1 ...</k>
    <code> C1:String => C2 </code>
    <codeStack>... ListItem(C2:String) => .List </codeStack>

  rule
    <k> beginBasicBlock => .K ...</k>
    <heapMemory> _:Map => #initialize("heapMemory", "Map") </heapMemory>
    <stackMemory> _:Map => #initialize("stackMemory", "Map") </stackMemory>
    <out> _:List => .List </out>
  rule
    <k> endBasicBlock => addCode(#generate(M1, M2, L, .K))  ...</k>
    <heapMemory> M1:Map </heapMemory>
    <stackMemory> M2:Map </stackMemory>
    <out> L:List => .List </out>
  rule
    <k> K:KItem ~> endBasicBlock => addCode(#generate(M1, M2, L, K)) ...</k>
    <heapMemory> M1:Map </heapMemory>
    <stackMemory> M2:Map </stackMemory>
    <out> L:List => .List </out>
    when isTypedValue(K) orBool isBool(K)

  rule
    <k> addCode(C2:String) => .K ...</k>
    <code>
      C1:String => #if C1 =/=K "" #then C1 +String "; " +String C2 #else C2 #fi
    </code>

  syntax KItem ::= if(Expression, Statement, Statement)
                 | choice(Expression, Expression, Expression)
                 | while(Expression, Statement)
  syntax KResult ::= String
  syntax Expression ::= String
  syntax Statement ::= String
  rule if(E, S1, S2) => extendedBlock(expression2bool(E)) ~> if(HOLE, S1, S2)            [heat]
  rule K:KResult ~> if(HOLE, S1, S2) => if(K, S1, S2)                   [cool]
  rule if(E, S1, S2) => extendedBlock(S1) ~> if(E, HOLE, S2)            [heat]
  rule K:KResult ~> if(E, HOLE, S2)  => if(E, K, S2)                    [cool]
  rule if(E, S1, S2) => extendedBlock(S2) ~> if(E, S1, HOLE)            [heat]
  rule K:KResult ~> if(E, S1, HOLE)  => if(E, S1, K)                    [cool]
  rule choice(E1, E2, E3) => extendedBlock(expression2bool(E1)) ~> choice(HOLE, E2, E3)  [heat]
  rule K:KResult ~> choice(HOLE, E1, E2) => choice(K, E1, E2)           [cool]
  rule choice(E1, E2, E3) => extendedBlock(E2) ~> choice(E1, HOLE, E3)  [heat]
  rule K:KResult ~> choice(E1, HOLE, E2) => choice(E1, K, E2)           [cool]
  rule choice(E1, E2, E3) => extendedBlock(E3) ~> choice(E1, E2, HOLE)  [heat]
  rule K:KResult ~> choice(E1, E2, HOLE) => choice(E1, E2, K)           [cool]
  rule while(E, S) => extendedBlock(expression2bool(E)) ~> while(HOLE, S)                [heat]
  rule K:KResult ~> while(HOLE, S) => while(K, S)                       [cool]
  rule while(E, S) => extendedBlock(S) ~> while(E, HOLE)                [heat]
  rule K:KResult ~> while(E, HOLE) => while(E, K)                       [cool]

  rule if (E) S1 else S2 => endBasicBlock ~> if(E, S1, S2)      ~> beginBasicBlock
  rule E1 ? E2 : E3      => endBasicBlock ~> choice(E1, E2, E3) ~> beginBasicBlock
  rule while (E) S       => endBasicBlock ~> while(E, S)        ~> beginBasicBlock

  rule if(E:String, S1:String, S2:String)
    => addCode("(if " +String E +String " then " +String S1 +String " else " +String S2 +String ")")
  rule choice(E1:String, E2:String, E3:String)
    => addCode("(if " +String E1 +String " then " +String E2 +String " else " +String E3 +String ")")
  rule while(E:String, S:String)
    => addCode("while " +String E +String " do " +String S +String "done")

  rule _:TypedValue; => endBasicBlock ~> beginBasicBlock    [structural]

  syntax Value ::= call(Id, Values)
  syntax TypedValue ::= return(Value)
  rule
    <k> F:Id(EEs:EvaluatedExpressions) => tv(T, call(F, getArgumentValues(EEs))) ...</k>
    <fun>... F |-> functionBody(_:ParameterDeclarations, T:Type, _:Block) ...</fun>
  rule
    <k>
      return tv(T:Type, V:Value);
    =>
      deleteLocals(values(Env)) ~> return(V) ~> endBasicBlock// ~> endExtendedBlock
    ...</k>
    <env> Env:Map </env>
    <fun>... F |-> functionBody(_:ParameterDeclarations, T:Type, _:Block) ...</fun>
    <fun-id> F:Id </fun-id>

  syntax KItem ::= formatInt(String, Value)
                 | formatString(String)
  rule
    <k> printf(S:String, tv(int, V:Value)) => tv(void, undef) ...</k>
    <out>... .List => ListItem(formatInt(S, V)) </out>
  rule
    <k> printf(S:String) => tv(void, undef) ...</k>
    <out>... .List => ListItem(formatString(S)) </out>
  //rule malloc(EEs:EvaluatedExpressions) => tv(void *, call(F, EEs))
  //rule F:Id(EEs:EvaluatedExpressions) => tv(void, call(F, getArgumentValues(EEs)))
  //  requires F ==K free orBool F ==K scanf

  syntax KItem ::= "generate1"
                 | generate2(Set)
                 | generate3(Id)
                 | generate4(Id, EvaluatedExpressions)
  rule
    <k> generate1 => generate2(keys(Funs)) </k>
    <fun> Funs:Map </fun>
  rule (.K => generate3(F)) ~> generate2((SetItem(F:Id) => .Set) S:Set)
  rule
    <k> generate3(F:Id) => generate4(F, makeTypedArguments(PDs)) ...</k>
    <fun>... F |-> functionBody(PDs:ParameterDeclarations, _:Type, _:Block) ...</fun>
  rule
    <k>
      generate4(F:Id, EEs:EvaluatedExpressions)
    =>
      addString("let rec " +String Id2String(F) +String getParameterNames(EEs) +String " =\ntry\n")
      ~> extendedBlock({ declareParameters(PDs) bindParameters(PDs, EEs, B) })
      //~> addString("\nwith Return return_value -> return_value\n;;\n")
    ...</k>
    <fun>... F |-> functionBody(PDs:ParameterDeclarations, _:Type, B:Block) ...</fun>
    <fun-id> _ => F </fun-id>

  rule
    <k> addString(C2:String) => .K ...</k>
    <code> C1:String => C1 +String C2 </code>

  rule
    <k> (C2:String => .K) ~> generate2(_:Set) </k>
    <code> C1:String => C1 +String C2 +String ";\n(C_value_int 0)\nwith Return return_value -> return_value\n;;\n" </code>
  rule
    <k> generate2(.Set) => .K </k>
    <code> C:String </code>
    <stdout>...
      .List
    =>
      ListItem(""
        +String "type c_pointer = C_pointer_object of int | C_pointer_null;;\n"
        +String "type c_type = C_type_int | C_type_double | C_type_pointer of c_type | C_type_struct of string;;\n"
        +String "type c_value = C_value_int of int | C_value_float of float | C_value_pointer of c_pointer | C_value_undef;;\n"
        +String "type c_typed_value = C_typed_value of c_type * c_value;;\n"
        +String "module C_pointer = struct type t = c_pointer let compare : t -> t -> int = compare end;;\n"
        +String "module HeapMemoryMap = Map.Make(C_pointer);;\n"
        +String "module ObjectMap = Map.Make(String);;\n"
        +String "module StackMemoryMap = Map.Make(C_pointer);;\n"
        +String "exception Side_Condition_Failure;;\n"
        +String "exception Return of c_value;;\n"
        +String "let ite x y z = if x then y else z;;\n"
        +String "let print_int s v = match v with (C_value_int n) -> Printf.printf s n;;"
        +String ""
        +String "let stackMemoryRef = ref StackMemoryMap.empty;;\n"
        +String "let heapMemoryRef = ref HeapMemoryMap.empty;;\n"
        +String C +String "\n"
        +String "match main with (C_value_int n) -> n;;\n")
    </stdout>

  syntax EvaluatedExpressions ::= makeTypedArguments(ParameterDeclarations)    [function]
  rule makeTypedArguments(T:Type _:Id, PDs:ParameterDeclarations)
    =>  valueOfType(T), makeTypedArguments(PDs)
  rule makeTypedArguments(.ParameterDeclarations) => .EvaluatedExpressions
  syntax TypedValue ::= valueOfType(Type)   [function]
  rule valueOfType(int) => tv(int, ?_:Int)
  rule valueOfType(double) => tv(double, ?_:Float)
  rule valueOfType(T:Type *) => tv(T:Type *, ?_:Pointer)
  syntax String ::= getParameterNames(EvaluatedExpressions)   [function]
  rule getParameterNames(tv(_:Type, V:Value), EEs:EvaluatedExpressions)
    => " " +String #name(V) +String getParameterNames(EEs)
  rule getParameterNames(.EvaluatedExpressions) => ""
  syntax Values ::= getArgumentValues(EvaluatedExpressions)   [function]
  rule getArgumentValues(tv(_:Type, V:Value), EEs:EvaluatedExpressions)
    => V, getArgumentValues(EEs)
  rule getArgumentValues(.EvaluatedExpressions) => .Values

  syntax Values ::= List{Value, ","}

  syntax Int ::= ite(Bool, Int, Int)    [function]
endmodule
