--------------------------------- MODULE AB ---------------------------------
EXTENDS Naturals, Sequences, FiniteSets, SequencesExt, SequenceTheorems, NaturalsInduction, SequencesExtTheorems, SequencePartitionTheorems

CONSTANT Data

(***************************************************************************)
(* We first define Remove(i, seq) to be the sequence obtained by removing  *)
(* element number i from sequence seq.                                     *)
(***************************************************************************)
Remove2(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]                                         

VARIABLES BVar, AVar,  \* The same as in module ABSpec
          AtoB,  \* The sequence of data messages in transit from sender to receiver.
          BtoA   \* The sequence of ack messages in transit from receiver to sender.
                 \* Messages are sent by appending them to the end of the sequence.
                 \* and received by removing them from the head of the sequence.

vars == << AVar, BVar, AtoB, BtoA >>

Seq2(S) == UNION {[1..n -> S] : n \in 0..3}

ProdSeq == UNION {[1..n -> Data \X {0,1}] : n \in 0 .. Cardinality(Data \X {0,1})}
nseq == UNION {[1..n -> {0,1}] : n \in 0 .. Cardinality({0,1})}
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
        
ARcv == /\ BtoA # << >> \* always remove head from BtoA. But if bits are equal then AVar = BVar and AVar' update
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<AtoB, BVar>>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>
   
BRcv == /\ AtoB # << >> \* always remove head from AtoB. But if bits are unequal then BVar' = Head(AtoB) = AVar update
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB): 
                         AtoB' = Remove2(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA): 
                         BtoA' = Remove2(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED << AVar, BVar >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg


Spec == Init /\ [][Next]_vars

FlipPositions(seq) == {i \in 1..(Len(seq)-1) : seq[i] # seq[i+1]}

OnlyOneFlip(seq) == Cardinality(FlipPositions(seq)) < 2                                                                        
  
       
\* seems correct. if Head(BtoA) = AVar[2]. Thats the ack which A awaited. So on receive of the ack there is consesus about the state. Namely A know that Avar = BVar 
\* A flips the bit after receiving the ack. This is the preparation for the new ASnd action.
CheckInv1 ==  \/ BtoA = << >> 
              \/ Head(BtoA) = AVar[2] => AVar = BVar

\* seems also correct. This is the case when B recieves a new message from the ASnd action. Only if the bit flip is detected by B then the message is processed. 
\* At that point in time the states are still AVar[1] = BVar[1]. The bit however is flipped at that point in time. So AVar[2] = 1 - BVar[2]  
CheckInv2 ==  \/ AtoB = << >> 
              \/  Head(AtoB)[2] # BVar[2] => AVar = Head(AtoB)   
              

\* An invariant I is inductive, iff Init => I and I /\ [Next]_vars => I. Note
\* though, that TypeInv itself won't imply Invariant though!  TypeInv alone
\* does not help us prove Invariant.
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)
InvSend == \A i \in 1..Len(AtoB): (AtoB[i][2] = AVar[2] => AtoB[i] = AVar )
Toggle == Ordered(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
IndInv ==  /\ TypeInv
           /\ Inv
           /\ Toggle
           /\ InvSend
           
IndInv1 ==  /\ TypeInv
               /\ CheckInv1
               /\ Toggle
               /\ InvSend    
               
IndInv2 ==  /\ TypeInv
               /\ CheckInv2
               /\ Toggle
               /\ InvSend                          

-----------------------------------------------------------------------------
ABS == INSTANCE ABSpec

INSTANCE TLAPS

THEOREM IndInvProof == Spec => []IndInv 
    <1>1a Init => TypeInv BY DEF Init, TypeInv
    <1>1b Init => Inv BY DEF Init, Inv    
    <1>1c Init => Toggle BY DEF Init, Toggle, Ordered, Reverse, SecondElFromSeq, Ordered1, Ordered2
    <1>1d Init => InvSend BY DEF Init, InvSend         
    <1>1. Init => IndInv BY <1>1a, <1>1b, <1>1c, <1>1d DEF IndInv
    <1>2. IndInv /\ [Next]_vars => IndInv'
    <1> QED BY <1>1, <1>2, PTL DEF Spec 

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
        <3>5. CASE LoseMsg BY <2>1, <3>5 DEF TypeInv, LoseMsg, Remove2
        <3>6. QED
          BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5 DEF Next
      <2>2. CASE UNCHANGED vars BY <2>2 DEF TypeInv, vars 
      <2>3. QED
        BY <2>1, <2>2
    <1> QED BY <1>1, <1>2, PTL DEF Spec 
    
    
THEOREM Invariance == Spec => []Inv 
    <1>1. Spec => []IndInv BY  IndInvProof
    <1>4. IndInv => Inv BY DEF IndInv, Inv
    <1>5. QED BY <1>1, <1>4, PTL DEF Spec
    
THEOREM Invariance2 == Spec => []InvSend 
    <1>1. Spec => []IndInv BY  IndInvProof
    <1>4. IndInv => InvSend BY DEF IndInv, InvSend
    <1>5. QED BY <1>1, <1>4, PTL DEF Spec    
    
THEOREM Invariance3 == Spec => []Toggle 
    <1>1. Spec => []IndInv BY  IndInvProof
    <1>4. IndInv => Toggle BY DEF IndInv, Toggle
    <1>5. QED BY <1>1, <1>4, PTL DEF Spec  
    
    
THEOREM Refinement2 == Spec => ABS!Spec
    <1>i. Init => ABS!Init BY DEF Init, ABS!Init
    <1>1. Spec => []Inv BY Invariance
    <1>2. IndInv /\ IndInv' /\ [Next]_vars => [ABS!Next]_ABS!vars
      <2> SUFFICES ASSUME [Next]_vars, IndInv, IndInv'
                   PROVE  [ABS!Next]_ABS!vars
        OBVIOUS
      <2>q QED
        <3>1. CASE Next
          <4>1. CASE ASnd
            <5> USE DEF Next, ASnd, ABS!vars
            <5>1. UNCHANGED << AVar, BVar >>
                <6>1. UNCHANGED <<AVar, BtoA, BVar>> BY <4>1
                <6> QED BY <6>1
            <5>2. QED BY <5>1 
          <4>2. CASE BSnd
            <5> USE DEF Next, BSnd, ABS!vars
            <5>1. UNCHANGED << AVar, BVar >>
                <6>1. UNCHANGED <<AVar, AtoB, BVar>> BY <4>2
                <6> QED BY <6>1  
            <5>2. QED BY <5>1
          <4>3. CASE ARcv      
            <5>1. CASE Head(BtoA) # AVar[2]
                <6> USE DEF Next, ARcv, ABS!vars
                <6>1. UNCHANGED BVar BY <4>3
                <6>2. UNCHANGED AVar BY <4>3, <5>1  
                <6>3. QED BY <6>1, <6>2
            <5>2. CASE Head(BtoA) = AVar[2]                 
            <5>3. QED BY <5>1, <5>2                                                         
          <4>4. CASE BRcv  
            <5> USE DEF Next, BRcv, ABS!vars
            <5>1. CASE Head(AtoB)[2] = BVar[2]
                <6>1. UNCHANGED AVar BY <4>4
                <6>2. UNCHANGED BVar BY <4>4, <5>1
                <6>3. QED BY <6>1, <6>2
            <5>2. CASE Head(AtoB)[2] # BVar[2]
                <6> USE DEF ABS!Next, ABS!B
                <6>1. UNCHANGED AVar BY <4>4   
                <6>3. BVar' = AVar
                    <7>1. BVar' = Head(AtoB) BY <4>4, <5>2
                    <7>2. Head(AtoB)[2] = AVar[2]
                        <8>2. Ordered(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                            <9>1. Ordered(BtoA \o (<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>))
                                <10>1. Ordered(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)  BY DEF IndInv, Toggle
                                <10>2. BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>> = BtoA \o (<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                    <11>1. BtoA \in Seq({0,1}) BY DEF TypeInv, IndInv
                                    <11>2. <<AVar[2]>> \in Seq({0,1}) BY DEF TypeInv, IndInv
                                    <11>2a <<BVar[2]>> \in Seq({0,1}) BY DEF TypeInv, IndInv
                                    <11>2b SecondElFromSeq(AtoB)  \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                                    <11>3. <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                                    <11>4. (BtoA \o (<<BVar[2]>> \o SecondElFromSeq(AtoB))) \o <<AVar[2]>> = BtoA \o ((<<BVar[2]>> \o SecondElFromSeq(AtoB)) \o <<AVar[2]>>) BY <11>1, <11>2, <11>3, ConcatAssociative
                                    <11>5. BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) = BtoA \o (<<BVar[2]>> \o SecondElFromSeq(AtoB))BY <11>1, <11>2a, <11>2b, ConcatAssociative 
                                    <11>q QED BY <11>4, <11>5
                                <10>q QED BY <10>1, <10>2 DEF IndInv, Toggle
                            <9>2. BtoA \in Seq({0,1}) BY DEF TypeInv, IndInv
                            <9>3. (<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                            <9>q QED BY <9>1, <9>2, <9>3, OrderPartitionr, ConcatAssociative                        
                        <8>4. Ordered(SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                            <9>1. SecondElFromSeq(AtoB) \o <<AVar[2]>> \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                            <9>2. <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>> = <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                <10>1. <<BVar[2]>> \in Seq({0,1}) BY DEF TypeInv, IndInv
                                <10>2. SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                                <10>3. <<AVar[2]>> \in Seq({0,1}) BY DEF TypeInv, IndInv
                                <10>q QED BY <10>1, <10>2, <10>3
                            <9>q QED BY <8>2, <9>1, <9>2, OrderPartitionr DEF IndInv, TypeInv, Reverse                                          
                        <8>3a. BVar[2] \in {0, 1} BY DEF IndInv, TypeInv
                        <8>3b. Head(AtoB)[2] \in {0, 1}   BY <4>4, ElementOfSeq DEF IndInv, TypeInv, BRcv                                            
                        <8>3. Head(AtoB)[2] > BVar[2] \/ Head(AtoB)[2] < BVar[2] BY <5>2, <4>4, ElementOfSeq DEF IndInv, TypeInv, BRcv   
                        <8>6. CASE Head(AtoB)[2] > BVar[2]
                            <9>1. AVar[2] \in {0,1} BY DEF IndInv, TypeInv
                            <9>2. Head(AtoB)[2] \in {0,1} BY <8>3b
                            <9>3. BVar[2] \in {0,1} BY DEF TypeInv, IndInv   
                            <9>4. BVar[2] = 0 BY <9>2, <9>3, <8>6 
                            <9>5. Head(AtoB)[2] = 1 BY <9>2, <9>3, <8>6  
                            <9>5aa. AtoB \in Seq(Data \X {0,1}) BY DEF TypeInv, IndInv    
                            <9>5bb. AtoB # << >>  BY <4>4 DEF BRcv                               
                            <9>8 Head(AtoB)[2] = Head(SecondElFromSeq(AtoB)) BY <9>5aa, <9>5bb, SeqComm                             
                            <9>5b. SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq                            
                            <9>6. Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)    
                                <10>2. ASSUME Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>) PROVE FALSE
                                    <11>a SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq      
                                    <11>b <<BVar[2]>> \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq     
                                    <11>c Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB)) BY <10>2, <9>1, <9>3, <9>5b, OrderPartition2   
                                    <11>d 1 \in 1..Len(SecondElFromSeq(AtoB))     
                                        <12>0. SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF IndInv, TypeInv, SecondElFromSeq   
                                        <12>1. SecondElFromSeq(AtoB) # << >>
                                            <13>1. AtoB # << >> BY <4>4 DEF BRcv
                                            <13>2. AtoB \in Seq(Data \X {0,1}) BY DEF TypeInv, IndInv
                                            <13>q QED BY <13>1, <13>2 DEF SecondElFromSeq
                                        <12>3. Len(SecondElFromSeq(AtoB)) >= 1 BY EmptySeq, <12>1, <12>0
                                        <12>q QED BY <12>3                          
                                    <11>1. BVar[2] >= SecondElFromSeq(AtoB)[1] BY <11>a, <11>b, <11>c, <11>d, OrderPartitionConcatElem2L
                                    <11>2. BVar[2] >= Head(AtoB)[2] BY <11>1, <9>8 DEF SecondElFromSeq, Head                                 
                                    <11>q QED BY <11>2, <9>5, <9>4                                 
                                <10>q QED BY <8>2, <10>2 DEF Ordered   
                            <9>7. AVar[2] = 1
                                <10>1. BVar[2] \in {0,1} BY DEF IndInv, TypeInv
                                <10>3. SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF IndInv, TypeInv, SecondElFromSeq   
                                <10>4. BVar[2] < AVar[2] 
                                    <11>1. BVar[2] <= AVar[2] BY <9>6, <9>1, <10>1, <10>3, OrderPartitionConcatElem1LR2
                                    <11>2. <<BVar[2]>> \in Seq({0,1}) BY <9>3
                                    <11>3. <<AVar[2]>> \in Seq({0,1}) BY <9>1                                   
                                    <11>4. <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>> = <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>) BY ConcatAssociative, <11>3, <11>2, <9>5b, <11>2
                                    <11>5. (SecondElFromSeq(AtoB) \o <<AVar[2]>>) \in Seq({0,1}) BY <9>5b, <11>3                                    
                                    <11>6. Ordered1(SecondElFromSeq(AtoB) \o <<AVar[2]>>) BY <9>6, <11>2,<11>3,<11>4, <11>5, OrderPartition1r
                                    <11>7. Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB)) BY <9>6, <11>2,<11>3, <9>5b, OrderPartition1
                                    <11>8a SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv     
                                    <11>8b AtoB # << >>  BY <4>4 DEF BRcv, SecondElFromSeq
                                    <11>8. Head(SecondElFromSeq(AtoB)) <= AVar[2] 
                                        <12>1 SecondElFromSeq(AtoB) = <<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) BY HeadTailPart, <9>5b, <11>8a
                                        <12>2 Ordered1(<<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) \o <<AVar[2]>>) BY <12>1, <11>6 
                                        <12>3 Tail(SecondElFromSeq(AtoB)) \in Seq({0,1}) BY  <9>5b, <11>8a, HeadTailProperties
                                        <12>4 <<Head(SecondElFromSeq(AtoB))>> \in Seq({0,1}) BY  <9>5b, <11>8a, HeadTailProperties
                                        <12>q QED BY <12>1, <12>2, <12>3, <12>4, <11>3, <9>5b, OrderPartitionConcatElem1LR2, HeadTailProperties 
                                    <11>9. BVar[2] < Head(SecondElFromSeq(AtoB)) BY <8>6 , <9>8
                                    <11>10a SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                    <11>10b SecondElFromSeq(AtoB) # << >>     
                                        <12>1. AtoB # << >> BY <4>4 DEF BRcv
                                        <12>2. AtoB \in Seq(Data \X {0,1}) BY DEF TypeInv, IndInv
                                        <12>q QED BY <12>1, <12>2 DEF SecondElFromSeq
                                    <11>10. Head(SecondElFromSeq(AtoB)) \in {0,1} BY <11>10a, <11>10b, HeadTailProperties DEF Head, Seq
                                    <11>11. BVar[2] \in Nat BY DEF IndInv, TypeInv
                                    <11>12. AVar[2] \in Nat BY DEF IndInv, TypeInv                               
                                    <11>q QED BY <11>8, <11>9, <11>10, <11>11, <11>12, LesserTrans 
                                <10>q QED  BY <10>4, <9>4, <9>1, <9>3                                   
                            <9>q QED BY <9>5, <9>7
                        <8>5. CASE Head(AtoB)[2] < BVar[2] 
                        <8>q QED BY <8>2, <8>4, <8>3, <8>6, <8>5 
                    <7>6. Head(AtoB) = AVar
                        <8>1. AtoB # << >> BY <4>4 DEF BRcv
                        <8>2. AtoB \in Seq(Data \X {0,1}) BY DEF IndInv, TypeInv   
                        <8>3. Len(AtoB) >= 1 BY EmptySeq, <8>1, <8>2
                        <8>q QED BY <7>2, <8>3 DEF IndInv, InvSend, Head                    
                    <7>q QED BY <7>1, <7>6
                <6>4. AVar[2] # BVar[2]              
                <6>q. QED BY <6>1, <6>3, <5>2, <6>4              
            <5>3. QED BY <5>1, <5>2            
          <4>5. CASE LoseMsg
            <5> USE DEF Next, LoseMsg, ABS!vars
            <5>1. UNCHANGED << AVar, BVar >> BY <4>5
            <5>2. QED BY <5>1            
          <4>6. QED
            BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5 DEF Next
        <3>2. CASE UNCHANGED vars BY <3>2 DEF vars, ABS!Next, ABS!vars
        <3>3. QED
          BY <3>1, <3>2    
    <1>3. QED BY <1>i, <1>1, <1>2, PTL DEF Spec, ABS!Spec
    

-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with fairness conditions added.                        *)
(***************************************************************************)
FairSpec == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                      WF_vars(ASnd) /\ WF_vars(BSnd)
=============================================================================
\* Modification History
\* Last modified Sun Feb 23 18:27:17 CET 2025 by appeltwi
\* Last modified Tue Dec 31 18:19:05 CET 2024 by appeltwi
\* Last modified Wed Dec 27 13:29:51 PST 2017 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
