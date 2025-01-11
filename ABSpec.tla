------------------------------ MODULE ABSpec --------------------------------
EXTENDS Integers

CONSTANT Data  \* The set of all possible data values.

VARIABLES AVar,   \* The last <<value, bit>> pair A decided to send.
          BVar    \* The last <<value, bit>> pair B received.
          
(***************************************************************************)
(* Type correctness means that AVar and BVar are tuples <<d, i>> where     *)
(* d \in Data and i \in {0, 1}.                                            *)
(***************************************************************************)
TypeOK == /\ AVar \in Data \X {0,1}
          /\ BVar \in Data \X {0,1}

(***************************************************************************)
(* It's useful to define vars to be the tuple of all variables, for        *)
(* example so we can write [Next]_vars instead of [Next]_<< ...  >>        *)
(***************************************************************************)
vars == << AVar, BVar >>


(***************************************************************************)
(* Initially AVar can equal <<d, 1>> for any Data value d, and BVar equals *)
(* AVar.                                                                   *)
(***************************************************************************)
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

(***************************************************************************)
(* When AVar = BVar, the sender can "send" an arbitrary data d item by     *)
(* setting AVar[1] to d and complementing AVar[2].  It then waits until    *)
(* the receiver "receives" the message by setting BVar to AVar before it   *)
(* can send its next message.  Sending is described by action A and        *)
(* receiving by action B.                                                  *)
(***************************************************************************)
A == /\ AVar = BVar
     /\ \E d \in Data: /\ AVar' = <<d, 1 - AVar[2]>> 
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* For understanding the spec, it's useful to define formulas that should  *)
(* be invariants and check that they are invariant.  The following         *)
(* invariant Inv asserts that, if AVar and BVar have equal second          *)
(* components, then they are equal (which by the invariance of TypeOK      *)
(* implies that they have equal first components).                         *)
(***************************************************************************)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)
IndInv == /\ TypeOK
          /\ Inv
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with the addition requirement that it keeps taking     *)
(* steps.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next) 

INSTANCE TLAPS

THEOREM TypeCorrect == Spec => []TypeOK 
    <1>1. Init => TypeOK BY SMT DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK' BY SMT DEF TypeOK, Init, Next, A, B, vars
    <1>3. QED BY <1>1, <1>2, PTL DEF Spec
    
SendDataEventuallyReceived == \A v \in Data \X {0, 1}: (AVar = v) ~> (BVar = v)

THEOREM Invariance == Spec => [] Inv 
    <1>1. Init => IndInv 
      <2> SUFFICES ASSUME Init
                   PROVE  IndInv
        OBVIOUS
      <2>1. TypeOK BY DEF Init, TypeOK
      <2>2. Inv BY DEF Init, TypeOK
      <2>3. QED
        BY <2>1, <2>2 DEF IndInv
    <1>2. IndInv /\ [Next]_vars =>  IndInv' BY DEF TypeOK, IndInv, Inv, Next, A, B, vars
    <1>3. IndInv => Inv BY DEF IndInv
    <1>4. QED BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec
    
THEOREM FairSpecToSpec == FairSpec => Spec BY DEF FairSpec
=============================================================================
\* Modification History
\* Last modified Sat Jan 04 20:44:19 CET 2025 by appeltwi
\* Last modified Sun Dec 29 14:21:45 CET 2024 by appeltwi
\* Last modified Wed Oct 18 04:07:37 PDT 2017 by lamport
\* Created Fri Sep 04 07:08:22 PDT 2015 by lamport

