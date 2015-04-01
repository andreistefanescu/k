// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module IMP-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule


module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
                  <k color="green"> beginExtendedBlock ~> $PGM:Pgm ~> endBasicBlock ~> endExtendedBlock </k>
                  <state color="red"> .Map </state>
                  <code> "" </code>
                  <codeStack> .List </codeStack>
                  <out stream="stdout"> .List </out>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I:Int ...</state>
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  //rule if (true)  S else _ => S
  //rule if (false) _ else S => S
  //rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ ...</k> <state> Rho:Map (.Map => X|->0) </state>
    when notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]


  syntax KItem ::= extendedBlock(K)
                 | "beginExtendedBlock"
                 | "endExtendedBlock"
                 | "beginBasicBlock"
                 | "endBasicBlock"
  syntax Map ::= "#initializeState()"                       [function, impure, hook(Gen:init)]
  syntax String ::= "#generateCode" "(" Map "," Value ")"   [function, impure, hook(Gen:gen)]
  syntax Value ::= Bool | Int

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
    <state> _:Map => #initializeState() </state>

  rule
    <k> endBasicBlock => #generateCode(State, .K) ...</k>
    <state> State:Map </state>
  rule
    <k> V:Value ~> endBasicBlock => #generateCode(State, V) ...</k>
    <state> State:Map </state>


  syntax KItem ::= if(BExp, Stmt, Stmt)
                 | while(BExp, Stmt)
  syntax KResult ::= String
  syntax BExp ::= String
  syntax Stmt ::= String
  rule if(E, S1, S2) => extendedBlock(E) ~> if(HOLE, S1, S2)    [heat]
  rule K:KResult ~> if(HOLE, S1, S2) => if(K, S1, S2)           [cool]
  rule if(E, S1, S2) => extendedBlock(S1) ~> if(E, HOLE, S2)    [heat]
  rule K:KResult ~> if(E, HOLE, S2)  => if(E, K, S2)            [cool]
  rule if(E, S1, S2) => extendedBlock(S2) ~> if(E, S1, HOLE)    [heat]
  rule K:KResult ~> if(E, S1, HOLE)  => if(E, S1, K)            [cool]
  rule while(E, S) => extendedBlock(E) ~> while(HOLE, S)        [heat]
  rule K:KResult ~> while(HOLE, S) => while(K, S)               [cool]
  rule while(E, S) => extendedBlock(S) ~> while(E, HOLE)        [heat]
  rule K:KResult ~> while(E, HOLE) => while(E, K)               [cool]

  rule if (E) S1 else S2 => endBasicBlock ~> if(E, S1, S2) ~> beginBasicBlock
  rule while (E) S       => endBasicBlock ~> while(E, S)   ~> beginBasicBlock

  rule if(E:String, S1:String, S2:String) => "(if " +String E +String " then " +String S1 +String " else " +String S2 +String ")"
  rule while(E:String, S:String)          => "while " +String E +String " do " +String S +String "done"

  rule
    <k> (C2:String => .K) ~> L:KLabel(_) ...</k>
    <code>
      C1:String => #if C1 =/=K "" #then C1 +String "; " +String C2 #else C2 #fi
    </code>
    requires L ==KLabel 'beginBasicBlock
      orBool L ==KLabel 'if
      orBool L ==KLabel 'while
      orBool L ==KLabel 'endExtendedBlock

  rule
    <k> C:String => .K </k>
    <codeStack> .List </codeStack>
    <out>...
      .List
    =>
      ListItem(
        "module ImpMap = Map.Make(String);;\n"
        +String "let stateRef = ref ImpMap.empty;;\n"
        +String C +String ";;\n"
        +String "ImpMap.iter (fun key value ->  print_string(key ^ \" \" ^ (string_of_int value)^ \"\\n\")) !stateRef;;\n")
    </out>
endmodule

