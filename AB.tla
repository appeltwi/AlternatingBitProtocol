--------------------------------- MODULE AB ---------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

(***************************************************************************)
(* We first define Remove(i, seq) to be the sequence obtained by removing  *)
(* element number i from sequence seq.                                     *)
(***************************************************************************)
Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]

VARIABLES AVar, BVar,   \* The same as in module ABSpec
          AtoB,  \* The sequence of data messages in transit from sender to receiver.
          BtoA   \* The sequence of ack messages in transit from receiver to sender.
                 \* Messages are sent by appending them to the end of the sequence.
                 \* and received by removing them from the head of the sequence.

vars == << AVar, BVar, AtoB, BtoA >>

TypeInv == /\ AVar \in Data \X {0,1}
          /\ BVar  \in Data \X {0,1}
          /\ AtoB \in Seq(Data \X {0,1})
          /\ BtoA \in Seq({0,1})

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >> 

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BtoA, BVar>>
        
ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<AtoB, BVar>>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>
   
BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB): 
                         AtoB' = Remove(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA): 
                         BtoA' = Remove(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED << AVar, BVar >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

AVarBar == AVar
BVarBar == BVar

Spec == Init /\ [][Next]_vars

Inv == (AVar[2] = BVar[2]) => (AVar = BVar)
       
IndInv == /\ TypeInv
          /\ Inv    
          
\* seems correct. if Head(BtoA) = AVar[2]. Thats the ack which A awaited. So on receive of the ack there is consesus about the state. Namely A know that Avar = BVar 
\* A flips the bit after receiving the ack. This is the preparation for the new ASnd action.
CheckInv1 ==  BtoA # << >> /\ Head(BtoA) = AVar[2] => AVar = BVar

\* seems also correct. This is the case when B recieves a new message from the ASnd action. Only if the bit flip is detected by B then the message is processed. 
\* At that point in time the states are still AVar[1] = BVar[1]. The bit however is flipped at that point in time. So AVar[2] = 1 - BVar[2]
CheckInv2 ==  AtoB # << >> /\ Head(AtoB)[2] # BVar[2] => AVar[2] = 1 - BVar[2]   
CheckInv3 ==  AtoB # << >> /\ Head(AtoB)[2] # BVar[2] => Head(AtoB) = AVar                  

-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec WITH AVar <- AVarBar, BVar <- BVarBar

INSTANCE TLAPS

THEOREM TypeCorrect == Spec => []TypeInv 
    <1>1. Init => TypeInv BY DEF Init, TypeInv
    <1>2. TypeInv /\ [Next]_vars => TypeInv'
      <2> SUFFICES ASSUME TypeInv,
                          [Next]_vars
                   PROVE  TypeInv'
        OBVIOUS
      <2>1. CASE Next 
        <3>1. CASE ASnd BY <2>1, <3>1 DEF TypeInv, ASnd
        <3>2. CASE ARcv BY <2>1, <3>2 DEF TypeInv, ARcv
        <3>3. CASE BSnd BY <2>1, <3>3 DEF TypeInv, BSnd
        <3>4. CASE BRcv BY <2>1, <3>4 DEF TypeInv, BRcv
        <3>5. CASE LoseMsg BY <2>1, <3>5 DEF TypeInv, LoseMsg, Remove
        <3>6. QED
          BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
      <2>2. CASE UNCHANGED vars BY <2>2 DEF TypeInv, vars 
      <2>3. QED
        BY <2>1, <2>2
    <1> QED BY <1>1, <1>2, PTL DEF Spec 
    
THEOREM Invariance == Spec => []Inv 
    <1>1. Init => IndInv 
      <2> SUFFICES ASSUME Init
                   PROVE  IndInv
        OBVIOUS
      <2>1. TypeInv BY DEF Init, TypeInv
      <2>2. Inv BY DEF Init, Inv
      <2>3. QED
        BY <2>1, <2>2 DEF IndInv
    <1>2. IndInv /\ [Next]_vars =>  IndInv'
      <2> SUFFICES ASSUME IndInv,
                          [Next]_vars
                   PROVE  IndInv'
        OBVIOUS
      <2>1. CASE Next
        <3>1. CASE ASnd BY <2>1, <3>1 DEF IndInv, Inv, TypeInv, ASnd
        <3>2. CASE BSnd BY <2>1, <3>2 DEF IndInv, Inv, TypeInv, BSnd
        <3>3. CASE ARcv
          <4>1. TypeInv' BY <3>3 DEF TypeInv, Next, IndInv, ARcv
          <4>2. Inv'
            <5> USE DEF Inv, Next, IndInv, ARcv
            <5>1. CASE Head(BtoA) # AVar[2]
                <6>1. UNCHANGED AVar BY <3>3, <5>1
                <6>2. UNCHANGED BVar BY <3>3 
                <6>q QED BY <6>1, <6>2
            <5>2. CASE Head(BtoA) = AVar[2]
                <6>1. CASE AVar[2] = BVar[2]
                    <7>2. AVar[2]' = 1 - AVar[2] BY <5>2, <3>3 
                    <7>3. UNCHANGED BVar BY <3>3
                    <7>4. BVar[2]' = 1 - AVar[2]' BY <7>2, <7>3, <6>1 DEF TypeInv     
                    <7>q QED BY <7>2, <7>3, <7>4 DEF TypeInv                                 
                <6>2. CASE AVar[2] # BVar[2]
                    <7>1. \E d \in Data : AVar[1]' = d BY <5>2, <3>3 
                    <7>2. AVar[2]' = 1 - AVar[2] BY <5>2, <3>3 
                    <7>3. UNCHANGED BVar BY <3>3
                    <7>4. BVar[2]' = AVar[2]' BY <7>2, <7>3, <6>2 DEF TypeInv     
                    <7>q QED
                        <8> SUFFICES ASSUME TRUE
                                     PROVE AVar' = BVar'
                            BY <7>4 DEF TypeInv  
                        <8>1. QED BY <7>1, <7>2, <7>3, <7>4  
                <6>q QED BY <6>1, <6>2               
            <5>q QED BY <3>3, <5>1, <5>2
          <4>3. QED BY <4>1, <4>2 DEF IndInv
        <3>4. CASE BRcv
          <4>1. TypeInv' BY <3>4 DEF TypeInv, Next, IndInv, BRcv
          <4>2. Inv'
            <5> USE DEF Inv, Next, IndInv, BRcv
            <5>1. CASE Head(AtoB)[2] = BVar[2]
                <6>1. UNCHANGED BVar BY <3>4, <5>1
                <6>2. UNCHANGED AVar BY <3>4 
                <6>q QED BY <6>1, <6>2
            <5>2. CASE Head(AtoB)[2] # BVar[2]
                <6>a. Head(AtoB) = AVar OBVIOUS
                <6>1. AVar[2] = 1 - BVar[2] BY <6>a, <5>2 DEF TypeInv               
                <6>2. BVar[2]' = AVar[2]'       
                    <7>2. AVar[2]' = AVar[2] BY <3>4                             
                    <7>4. BVar[2]' = AVar[2]'
                        <8>1. BVar[2]' = 1 - BVar[2] BY <5>2, <3>4 DEF  TypeInv                 
                        <8>q QED BY <6>1, <8>1, <7>2 
                    <7>q QED BY <7>4, <6>1, <7>2 DEF TypeInv
                <6>3. BVar' = AVar'
                    <7>1. BVar' = Head(AtoB) BY <3>4, <5>2
                    <7>3. UNCHANGED AVar BY <3>4                    
                    <7>q QED BY <7>1, <6>a, <7>3
                <6>q QED BY <6>1, <6>2, <6>3      
            <5>q QED BY <3>3, <5>1, <5>2          
          <4>3. QED BY <4>1, <4>2 DEF IndInv
        <3>5. CASE LoseMsg
          <4>1. UNCHANGED <<AVar, BVar>> BY <3>5 DEF LoseMsg        
          <4>2. TypeInv'
            <5>1. (/\ AVar \in Data \X {0,1})' BY <4>1 DEF IndInv, TypeInv
            <5>2. (BVar  \in Data \X {0,1})' BY <4>1 DEF IndInv, TypeInv
            <5>3. (AtoB \in Seq(Data \X {0,1}))'
              <6>1. CASE /\ \E i \in 1..Len(AtoB): 
                                 AtoB' = Remove(i, AtoB)
                         /\ BtoA' = BtoA
                <7> SUFFICES ASSUME NEW i \in 1..Len(AtoB),
                                    AtoB' = Remove(i, AtoB)
                             PROVE  (AtoB \in Seq(Data \X {0,1}))'
                  BY <6>1 
                <7> QED 
                    <8>1. Remove(i, AtoB) \in Seq(Data \X {0, 1}) BY DEF Remove, IndInv, TypeInv
                    <8>q QED BY <8>1 DEF IndInv, TypeInv
              <6>2. CASE /\ \E i \in 1..Len(BtoA): 
                                 BtoA' = Remove(i, BtoA)
                         /\ AtoB' = AtoB
                <7>2. UNCHANGED AtoB BY <3>5, <6>2 DEF IndInv, TypeInv, Next, LoseMsg
                <7>q QED BY <7>2 DEF IndInv, TypeInv
              <6>3. QED
                BY <3>5, <6>1, <6>2 DEF LoseMsg
            <5>4. (BtoA \in Seq({0,1}))'
              <6>1. CASE /\ \E i \in 1..Len(AtoB): 
                                 AtoB' = Remove(i, AtoB)                            
                         /\ BtoA' = BtoA
                <7>2. UNCHANGED BtoA BY <3>5, <6>1 DEF IndInv, TypeInv, Next, LoseMsg
                <7>q QED BY <7>2 DEF IndInv, TypeInv                              
              <6>2. CASE /\ \E i \in 1..Len(BtoA): 
                                 BtoA' = Remove(i, BtoA)
                         /\ AtoB' = AtoB
                <7> SUFFICES ASSUME NEW i \in 1..Len(BtoA),
                                    BtoA' = Remove(i, BtoA)
                             PROVE  (BtoA \in Seq({0,1}))'
                  BY <6>2 
                <7> QED
                    <8>1. Remove(i, BtoA) \in Seq({0, 1}) BY DEF Remove, IndInv, TypeInv
                    <8>q QED BY <8>1 DEF IndInv, TypeInv                
              <6>3. QED
                BY <3>5, <6>1, <6>2 DEF LoseMsg
            <5>5. QED
              BY <5>1, <5>2, <5>3, <5>4 DEF TypeInv
          <4>3. Inv'
            <5>q QED BY <4>1 DEF Inv, IndInv, vars          
          <4>q QED
            BY <4>2, <4>3 DEF IndInv
        <3>6. QED
          BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
      <2>2. CASE UNCHANGED vars 
        <3>1. TypeInv'
          BY <2>2 DEF IndInv, vars, Inv, TypeInv
        <3>2. Inv'
          <4> USE DEF IndInv, vars, Inv, TypeInv
          <4>q. QED BY <2>2 
        <3>3. QED
          BY <3>1, <3>2 DEF IndInv
      <2>3. QED
        BY <2>1, <2>2
    <1>3. IndInv => Inv BY DEF IndInv
    <1>4. QED BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec
   

THEOREM Refinement == Spec => ABS!Spec
    <1>1. Init => ABS!Init BY DEF Init, ABS!Init, AVarBar, BVarBar
    <1>2. TypeInv /\ [Next]_vars => [ABS!Next]_ABS!vars
      <2> SUFFICES ASSUME [Next]_vars, TypeInv
                   PROVE  [ABS!Next]_ABS!vars
        OBVIOUS
      <2>q QED
        <3>1. CASE Next
          <4>1. CASE ASnd
            <5> USE DEF Next, ASnd, ABS!vars, AVarBar, BVarBar
            <5>1. UNCHANGED << AVar, BVar >>
                <6>1. UNCHANGED <<AVar, BtoA, BVar>> BY <4>1
                <6> QED BY <6>1
            <5>2. QED BY <5>1 
          <4>2. CASE BSnd
            <5> USE DEF Next, BSnd, ABS!vars, AVarBar, BVarBar
            <5>1. UNCHANGED << AVar, BVar >>
                <6>1. UNCHANGED <<AVar, AtoB, BVar>> BY <4>2
                <6> QED BY <6>1  
            <5>2. QED BY <5>1
          <4>3. CASE ARcv
            <5>1. CASE Head(BtoA) # AVar[2]
                <6> USE DEF Next, ARcv, ABS!vars, AVarBar, BVarBar
                <6>1. UNCHANGED BVar BY <4>3
                <6>2. UNCHANGED AVar BY <4>3, <5>1  
                <6>3. QED BY <6>1, <6>2
            <5>2. CASE Head(BtoA) = AVar[2]    
                <6> USE DEF Next, ARcv, ABS!vars, ABS!Next, ABS!A, AVarBar, BVarBar
                <6>1. UNCHANGED BVar BY <4>3                
                <6>2. \E d \in Data : /\ AVar' = <<d, 1 - AVar[2]>> BY <5>2, <4>3
                <6>3. AVar = BVar
                <6>4. QED BY <6>1, <6>2, <6>3, <5>2               
            <5>3. QED BY <5>1, <5>2                                                     
          <4>4. CASE BRcv
            <5> USE DEF Next, BRcv, ABS!vars, AVarBar, BVarBar
            <5>1. CASE Head(AtoB)[2] = BVar[2]
                <6>1. UNCHANGED AVar BY <4>4
                <6>2. UNCHANGED BVar BY <4>4, <5>1
                <6>3. QED BY <6>1, <6>2
            <5>2. CASE Head(AtoB)[2] # BVar[2]
                <6> USE DEF ABS!Next, ABS!B
                <6>1. UNCHANGED AVar BY <4>4   
                <6>2. BVar' = AVar                       
                <6>4. QED BY <6>1, <6>2, <5>2   
            <5>3. QED BY <5>1, <5>2    
          <4>5. CASE LoseMsg
            <5> USE DEF Next, LoseMsg, ABS!vars, AVarBar, BVarBar
            <5>1. UNCHANGED << AVar, BVar >> BY <4>5
            <5>2. QED BY <5>1            
          <4>6. QED
            BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5 DEF Next
        <3>2. CASE UNCHANGED vars BY <3>2 DEF vars, ABS!Next, ABS!vars, AVarBar, BVarBar
        <3>3. QED
          BY <3>1, <3>2
    <1>3. QED BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, ABS!Spec
    
    
THEOREM Refinement2 == Spec => ABS!Spec
    <1>i. Init => ABS!Init BY DEF Init, ABS!Init, AVarBar, BVarBar
    <1>1. Spec => []Inv BY Invariance
    <1>2. Inv /\ Inv' /\ [Next]_vars => [ABS!Next]_ABS!vars
    <1>3. QED BY <1>i, <1>1, <1>2, PTL DEF Spec, ABS!Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with fairness conditions added.                        *)
(***************************************************************************)
FairSpec == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                      WF_vars(ASnd) /\ WF_vars(BSnd)
=============================================================================
\* Modification History
\* Last modified Sun Jan 05 20:40:25 CET 2025 by appeltwi
\* Last modified Tue Dec 31 18:19:05 CET 2024 by appeltwi
\* Last modified Wed Dec 27 13:29:51 PST 2017 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
