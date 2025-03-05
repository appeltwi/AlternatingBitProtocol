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
      <2> SUFFICES ASSUME IndInv /\ [Next]_vars
                   PROVE  IndInv'
        OBVIOUS
      <2>1. TypeInv'
        <3>1. CASE Next
          <4>1. CASE ASnd BY <3>1, <4>1 DEF IndInv, TypeInv, ASnd
          <4>2. CASE ARcv BY <3>1, <4>2 DEF IndInv, TypeInv, ARcv
          <4>3. CASE BSnd BY <3>1, <4>3 DEF IndInv, TypeInv, BSnd
          <4>4. CASE BRcv BY <3>1, <4>4 DEF IndInv, TypeInv, BRcv
          <4>5. CASE LoseMsg BY <3>1, <4>5 DEF IndInv, TypeInv, LoseMsg, Remove2
          <4> QED BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5 DEF Next
        <3>2. CASE UNCHANGED vars BY <3>2 DEF IndInv, TypeInv, vars
        <3> QED BY <3>1, <3>2
      <2>2. Inv'
        <3>1. CASE Next
          <4>1. CASE ASnd BY <3>1, <4>1 DEF IndInv, Inv, ASnd
          <4>2. CASE ARcv
            <5>1. CASE Head(BtoA) = AVar[2]
            <5>2. CASE Head(BtoA) # AVar[2]
                <6>1. UNCHANGED AVar BY <4>2, <5>2 DEF ARcv
                <6>2. UNCHANGED BVar BY <4>2, <5>2 DEF ARcv
                <6> QED BY <6>1, <6>2 DEF IndInv, Inv, ARcv
            <5> QED BY <5>1, <5>2 DEF ARcv
          <4>3. CASE BSnd BY <3>1, <4>3 DEF IndInv, Inv, BSnd
          <4>4. CASE BRcv
            <5>1. CASE Head(AtoB)[2] # BVar[2]
            <5>2. CASE Head(AtoB)[2] = BVar[2]
                <6>1. UNCHANGED AVar BY <4>4, <5>2 DEF BRcv
                <6>2. UNCHANGED BVar BY <4>4, <5>2 DEF BRcv
                <6> QED BY <6>1, <6>2 DEF IndInv, Inv, BRcv            
            <5> QED BY <5>1, <5>2 DEF BRcv
          <4>5. CASE LoseMsg BY <3>1, <4>5 DEF IndInv, Inv, LoseMsg, Remove2
          <4> QED BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5 DEF Next
        <3>2. CASE UNCHANGED vars BY <3>2 DEF IndInv, Inv, vars
        <3> QED BY <3>1, <3>2      
      <2>3. Toggle'
        <3>1. CASE Next
        <3>2. CASE UNCHANGED vars BY <3>2 DEF IndInv, Toggle, vars
        <3> QED BY <3>1, <3>2      
      <2>4. InvSend'
        <3>1. CASE Next
          <4>1. CASE ASnd 
            <5>1. AtoB' = Append(AtoB, AVar) BY <3>1, <4>1 DEF IndInv, InvSend, ASnd
            <5>2. \A i \in 1..Len(AtoB) : AtoB[i][2] = AVar[2] => AtoB[i] = AVar BY <3>1, <4>1 DEF IndInv, InvSend, ASnd
            <5>3. UNCHANGED AVar BY <3>1, <4>1 DEF IndInv, InvSend, ASnd
            <5>4. AVar \in Data \X {0, 1} BY DEF IndInv, TypeInv
            <5>5. AtoB \in Seq(Data \X {0,1})  BY DEF IndInv, TypeInv
            <5>6. \A i \in 1..Len(AtoB) : AtoB'[i] = AtoB[i] BY <5>1, <5>4, <5>5, AppendProperties
            <5>7. \A i \in 1..Len(AtoB) : AtoB'[i][2] = AVar[2] => AtoB'[i] = AVar BY <5>6, <5>2 
            <5>8. Len(AtoB') = Len(AtoB) + 1 BY <5>1, <5>5, <5>4, AppendProperties
            <5>9. AtoB'[Len(AtoB')] = AVar BY <5>1, <5>4, <5>5, AppendProperties
            <5>10. AtoB'[Len(AtoB')][2] = AVar[2] => AtoB'[Len(AtoB')] = AVar BY <5>9
            <5>11. \A i \in 1..Len(AtoB'): IF i <= Len(AtoB) THEN AtoB'[i] = AtoB[i] ELSE AtoB'[Len(AtoB)+1] = AVar BY <5>1, <5>4, <5>5, AppendProperties2
            <5>13. \A i \in 1..Len(AtoB') : IF i <= Len(AtoB) THEN AtoB'[i][2] = AVar[2] => AtoB'[i] = AVar ELSE AtoB'[Len(AtoB')][2] = AVar[2] => AtoB'[Len(AtoB')] = AVar BY <5>7, <5>8, <5>10, <5>11
            <5>14. \A i \in 1..Len(AtoB') : AtoB'[i][2] = AVar[2] => AtoB'[i] = AVar
              <6> SUFFICES ASSUME NEW i \in 1..Len(AtoB')
                           PROVE  AtoB'[i][2] = AVar[2] => AtoB'[i] = AVar
                OBVIOUS
              <6>1. CASE i = Len(AtoB') BY <6>1, <5>10
              <6>2. CASE i < Len(AtoB')
                <7>1. i >= 1 OBVIOUS 
                <7>2. i <= Len(AtoB)
                    <8>1. Len(AtoB) \in Nat   BY DEF IndInv, TypeInv, LenProperties
                    <8> QED BY <5>8, <8>1, <6>2
                <7> QED BY <5>7, <7>1, <7>2
              <6> QED BY <6>1, <6>2
            <5> QED BY <5>14, <5>3 DEF IndInv, InvSend, ASnd
          <4>2. CASE ARcv BY <3>1, <4>2 DEF IndInv, InvSend, ARcv
          <4>3. CASE BSnd BY <3>1, <4>3 DEF IndInv, InvSend, BSnd
          <4>4. CASE BRcv BY <3>1, <4>4 DEF IndInv, InvSend, BRcv
          <4>5. CASE LoseMsg BY <3>1, <4>5 DEF IndInv, InvSend, LoseMsg, Remove2
          <4>6. QED
            BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5 DEF Next
        <3>2. CASE UNCHANGED vars BY <3>2 DEF IndInv, InvSend, vars
        <3> QED BY <3>1, <3>2      
      <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF IndInv
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
   
THEOREM Refinement == Spec => ABS!Spec
    <1>i. Init => ABS!Init BY DEF Init, ABS!Init
    <1>1. Spec => []IndInv BY IndInvProof
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
                <6> USE DEF  ABS!Next, ABS!A
                <6>1. UNCHANGED BVar BY <4>3 DEF Next, ARcv
                <6>2. AVar[2] = BVar[2]
                    <7>1. Ordered(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)  BY DEF IndInv, Toggle
                    <7>2. Ordered(<<Head(BtoA)>> \o (Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB)) \o <<AVar[2]>>) 
                        <8>1. <<Head(BtoA)>> \o Tail(BtoA) = BtoA
                            <9>1. BtoA # << >> BY <4>3 DEF ARcv 
                            <9>2. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                            <9> QED BY HeadTailProperties, <9>1, <9>2 
                        <8>2. Ordered(<<Head(BtoA)>> \o Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>) BY <8>1, <7>1
                        <8>3. <<Head(BtoA)>> \o (Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB)) \o <<AVar[2]>> = <<Head(BtoA)>> \o Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>
                            <9>0. BtoA # << >> BY <4>3 DEF ARcv
                            <9>1. <<Head(BtoA)>> \in Seq({0, 1}) BY <9>0 DEF TypeInv, IndInv
                            <9>2. Tail(BtoA) \in Seq({0, 1}) BY HeadTailProperties, <9>0 DEF TypeInv, IndInv
                            <9>3. <<BVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq     
                            <9>4. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                            <9>5. <<AVar[2]>> \in Seq({0, 1})  BY DEF TypeInv, IndInv, SecondElFromSeq                                              
                            <9> QED BY ConcatAssociative5, <9>1, <9>2, <9>3, <9>4, <9>5                       
                        <8> QED BY <8>3, <8>2
                    <7>3. Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq(Nat)
                        <8>1. BtoA # << >> BY <4>3 DEF ARcv
                        <8>2. SecondElFromSeq(AtoB) \in Seq(Nat) BY DEF TypeInv, IndInv, SecondElFromSeq
                        <8>3. <<BVar[2]>> \in Seq(Nat)  BY DEF TypeInv, IndInv
                        <8>4. Tail(BtoA) \in Seq(Nat) BY HeadTailProperties, <8>1 DEF TypeInv, IndInv
                        <8> QED BY ConcatProperties, <8>2, <8>3, <8>4
                    <7>4. Head(BtoA) \in Nat
                        <8>1. BtoA # << >> BY <4>3 DEF ARcv
                        <8> QED BY <8>1 DEF TypeInv, IndInv
                    <7>5. /\ AVar[2] \in Nat
                          /\ BVar[2] \in Nat BY DEF TypeInv, IndInv
                    <7>6. \E i \in 1..Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB)) : (Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))[i] = BVar[2]
                        <8> SUFFICES ASSUME 1 + Len(Tail(BtoA)) \in 1..Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))
                            PROVE (Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))[1 + Len(Tail(BtoA))] = BVar[2]
                            <9>1. 1 + Len(Tail(BtoA)) \in 1..Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))
                                <10>4. Len(Tail(BtoA)) \in Nat
                                       <11>1. Tail(BtoA) \in Seq({0, 1})
                                            <12>1. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                            <12>2. BtoA # << >> BY <4>3 DEF ARcv
                                            <12> QED BY <12>1,  <12>2, HeadTailProperties 
                                        <11> QED BY <11>1 ,LenProperties                                  
                                <10>1. 1 + Len(Tail(BtoA)) >= 1
                                    <11>3. Len(BtoA) \in Nat
                                        <12>1. BtoA \in Seq({0, 1})
                                            <13>1. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                            <13>2. BtoA # << >> BY <4>3 DEF ARcv
                                            <13> QED BY <13>1,  <13>2, HeadTailProperties 
                                        <12> QED BY <12>1 ,LenProperties                                                                              
                                    <11>1. Len(Tail(BtoA)) >= 0                            
                                        <12>1. BtoA # << >> BY <4>3 DEF ARcv
                                        <12>2. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                        <12>3. Len(BtoA) >= 1 BY EmptySeq, <12>1, <12>2
                                        <12>4. Len(Tail(BtoA)) = Len(BtoA) - 1 BY <12>1, <12>2, <12>3, HeadTailProperties
                                        <12>5. Len(BtoA) \in Nat BY <11>3
                                        <12>6. Len(Tail(BtoA)) \in Nat BY <10>4                                        
                                        <12>7. Len(Tail(BtoA)) + 1 = Len(BtoA) BY <12>4, <12>5, <12>6
                                        <12> QED BY <12>4, <12>3, <12>5, <12>6
                                    <11> QED BY <11>1, <10>4
                                <10>2. 1 + Len(Tail(BtoA)) <= Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))
                                    <11>1. Len(Tail(BtoA)) < Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))
                                        <12>1. Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB)) = Len(Tail(BtoA) \o <<BVar[2]>>) + Len(SecondElFromSeq(AtoB))
                                            <13>1. BtoA # << >> BY <4>3 DEF ARcv                                        
                                            <13>2. Tail(BtoA) \o <<BVar[2]>> \in Seq({0, 1}) BY ConcatProperties, HeadTailProperties, <13>1 DEF TypeInv, IndInv
                                            <13>3. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY  DEF TypeInv, IndInv, SecondElFromSeq
                                            <13> QED BY ConcatProperties, <13>2, <13>3
                                        <12>2. Len(Tail(BtoA) \o <<BVar[2]>>) = Len(Tail(BtoA)) + Len(<<BVar[2]>>)
                                            <13>1. BtoA # << >> BY <4>3 DEF ARcv                                            
                                            <13>2. Tail(BtoA) \in Seq({0, 1}) BY ConcatProperties, HeadTailProperties, <13>1 DEF TypeInv, IndInv
                                            <13>3. <<BVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                            <13> QED BY ConcatProperties, <13>2, <13>3
                                        <12>3. Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB)) = Len(Tail(BtoA)) + Len(<<BVar[2]>>) + Len(SecondElFromSeq(AtoB)) BY <12>1, <12>2
                                        <12>4. Len(Tail(BtoA)) \in Nat  BY <10>4
                                        <12>5. Len(<<BVar[2]>>) \in Nat BY DEF TypeInv, IndInv
                                        <12>6. Len(SecondElFromSeq(AtoB))  \in Nat BY  LenProperties DEF TypeInv, IndInv, SecondElFromSeq
                                        <12> QED BY <12>3, <12>4, <12>5, <12>6
                                    <11>2. Len(Tail(BtoA)) \in Nat BY <10>4
                                    <11>3. Len(Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB)) \in Nat
                                        <12>1. Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq({0, 1})
                                            <13>1. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY  DEF TypeInv, IndInv, SecondElFromSeq
                                            <13>2. <<BVar[2]>> \in Seq({0, 1}) BY  DEF TypeInv, IndInv
                                            <13>3. Tail(BtoA) \in Seq({0, 1})
                                                <14>1. BtoA # << >> BY <4>3 DEF ARcv 
                                                <14> QED BY HeadTailProperties, <14>1 DEF TypeInv, IndInv
                                            <13> QED BY ConcatProperties, <13>1, <13>2, <13>3 
                                        <12> QED BY <12>1, LenProperties
                                    <11> QED BY <11>1, <11>2, <11>3
                                <10>3. 1 + Len(Tail(BtoA)) \in Nat BY <10>4                             
                                <10> QED BY <10>1, <10>2, <10>3, <7>3
                            <9> QED BY <9>1
                        <8>1. (Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))[1 + Len(Tail(BtoA))] = BVar[2]
                            <9>1. (Tail(BtoA) \o <<BVar[2]>> \o SecondElFromSeq(AtoB))[1 + Len(Tail(BtoA))] = <<BVar[2]>>[1]
                                <10>1. Tail(BtoA) \in Seq({0, 1}) 
                                    <11>1. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>2. BtoA # << >> BY <4>3 DEF ARcv
                                    <11> QED BY <11>1,  <11>2, HeadTailProperties 
                                <10>2. <<BVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                <10>3. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                                <10> QED BY ConcatProperties, <10>1, <10>2, <10>3
                            <9> QED BY <9>1
                        <8>q QED BY <8>1
                    <7>q QED BY <5>2, <7>2, <7>3, <7>4, <7>5, <7>6, OrderBracket
                <6>3. \E d \in Data: AVar' = <<d, 1 - AVar[2]>> BY <5>2, <4>3 DEF Next, ARcv
                <6>q QED BY <6>1, <6>2, <6>3, <5>2             
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
                        <8>44. Ordered(<<BVar[2]>> \o SecondElFromSeq(AtoB))
                            <9>1. <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                            <9>q QED BY <8>2, <9>1, OrderPartition DEF IndInv, TypeInv, Reverse                                                                
                        <8>3a. BVar[2] \in {0, 1} BY DEF IndInv, TypeInv
                        <8>3b. Head(AtoB)[2] \in {0, 1}   BY <4>4, ElementOfSeq DEF IndInv, TypeInv, BRcv                                            
                        <8>3. Head(AtoB)[2] > BVar[2] \/ Head(AtoB)[2] < BVar[2] BY <5>2, <4>4, ElementOfSeq DEF IndInv, TypeInv, BRcv   
                        <8>6. CASE Head(AtoB)[2] # BVar[2]
                            <9>1. AVar[2] \in {0,1} BY DEF IndInv, TypeInv
                            <9>2. Head(AtoB)[2] \in {0,1} BY <8>3b
                            <9>3. BVar[2] \in {0,1} BY DEF TypeInv, IndInv   
                            <9>4. BVar[2] = 1 - Head(AtoB)[2] BY <9>2, <9>3, <8>6 
                            <9>5aa. AtoB \in Seq(Data \X {0,1}) BY DEF TypeInv, IndInv    
                            <9>5bb. AtoB # << >>  BY <4>4 DEF BRcv                               
                            <9>8. Head(AtoB)[2] = Head(SecondElFromSeq(AtoB)) BY <9>5aa, <9>5bb, SeqComm                             
                            <9>5b. SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                            <9>6b. \/ Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)  
                                   \/ Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>) BY <8>2 DEF  Ordered       
                            <9>6c. \/ Ordered1(SecondElFromSeq(AtoB) \o <<AVar[2]>>)  
                                   \/ Ordered2(SecondElFromSeq(AtoB) \o <<AVar[2]>>) BY <8>4 DEF  Ordered   
                            <9>6cc. \/ Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB))  
                                    \/ Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB)) BY <8>44 DEF  Ordered                                                                         
                            <9>6dd. BVar[2] <= AVar[2] \/ BVar[2] >= AVar[2] 
                                <10>1. <<BVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv 
                                <10>2. <<AVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv
                                <10>q QED BY <9>6b, <9>5b,<10>1, <10>2 , OrderPartitionConcatElem1LR2, OrderPartitionConcatElem2LR2    
                            <9>6d. BVar[2] # AVar[2]
                                <10>1. CASE Head(AtoB)[2] > BVar[2] 
                                    <11>1. Head(AtoB)[2] <= AVar[2]
                                        <12>1. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv
                                        <12>2. SecondElFromSeq(AtoB) = <<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) BY HeadTailPart, <9>5b, <12>1
                                        <12>3. Ordered1(SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                            <13>1. Ordered1(<<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>)) 
                                                <14>1. Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                                    <15>1. \/ Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB)  \o <<AVar[2]>>)  
                                                           \/ Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB)  \o <<AVar[2]>>) BY <8>2 DEF  Ordered  
                                                    <15>2. ASSUME Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB)  \o <<AVar[2]>>) PROVE FALSE
                                                        <16>1. Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB))
                                                            <17>1. <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF IndInv, TypeInv, SecondElFromSeq 
                                                            <17>2. <<AVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv 
                                                            <17>q QED BY OrderPartition2, <17>1, <17>2, <15>2
                                                        <16>2. Ordered2(<<BVar[2]>> \o (<<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)))) BY <12>2, <16>1
                                                        <16>3. Ordered2(<<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)))
                                                            <17>1. <<BVar[2]>> \o (<<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB))) =  <<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) 
                                                                <18>1. <<BVar[2]>> \in Seq({0, 1}) BY DEF IndInv, TypeInv, SecondElFromSeq 
                                                                <18>2. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                                                <18>3. <<Head(SecondElFromSeq(AtoB))>> \in Seq({0, 1}) BY <18>2 DEF IndInv, TypeInv, SecondElFromSeq 
                                                                <18>4. Tail(SecondElFromSeq(AtoB)) \in Seq({0, 1}) BY <18>2, <9>5b, HeadTailProperties 
                                                                <18>q QED BY ConcatAssociative, <18>1, <18>3, <18>4      
                                                            <17>q QED BY <17>1, <16>2                                                     
                                                        <16>4. Ordered2(<<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>>)
                                                            <17>2. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                                            <17>3. <<Head(SecondElFromSeq(AtoB))>> \in Seq({0, 1}) BY <17>2 DEF IndInv, TypeInv, SecondElFromSeq 
                                                            <17>4. Tail(SecondElFromSeq(AtoB)) \in Seq({0, 1}) BY <17>2, <9>5b, HeadTailProperties
                                                            <17>5. <<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>> \in Seq({0, 1})  BY <17>3 DEF IndInv, TypeInv, SecondElFromSeq                                                                
                                                            <17>q QED BY OrderPartition2, <16>3, <17>5, <17>4
                                                        <16>5. Ordered2(<<BVar[2]>> \o << >> \o <<Head(SecondElFromSeq(AtoB))>>)
                                                            <17>1. <<BVar[2]>> \o << >> = <<BVar[2]>> BY ConcatEmptySeq, <9>3
                                                            <17>q QED BY <16>4, <17>1
                                                        <16>6. Head(SecondElFromSeq(AtoB)) <= BVar[2]
                                                            <17>1. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv                                                         
                                                            <17>2. <<BVar[2]>> \in  Seq({0,1}) BY DEF IndInv, TypeInv
                                                            <17>3. <<Head(SecondElFromSeq(AtoB))>> \in  Seq({0,1}) BY <17>1 DEF IndInv, TypeInv, SecondElFromSeq 
                                                            <17>q QED BY <16>5, OrderPartitionConcatElem2LR2, <17>2, <17>3
                                                        <16>7. Head(AtoB)[2] <= BVar[2] BY <16>6, <9>8
                                                        <16>q QED BY <16>7, <10>1, <9>1, <9>2, <9>3
                                                    <15>q QED BY <15>1, <15>2
                                                <14>2. <<BVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv 
                                                <14>3. <<AVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv   
                                                <14>4. SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq                                               
                                                <14>q QED BY <14>1,<14>2,<14>3,<14>4, ConcatAssociative
                                            <13>2. <<BVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv
                                            <13>4. (SecondElFromSeq(AtoB) \o <<AVar[2]>>) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                            <13>q QED BY <13>1, <13>2, <13>4, OrderPartition1r
                                        <12>4. Ordered1(<<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) \o <<AVar[2]>>) BY <12>2, <12>3
                                        <12>5. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                        <12>6. Tail(SecondElFromSeq(AtoB)) \in Seq({0,1}) BY  <9>5b, <12>5, HeadTailProperties
                                        <12>8. AVar[2] \in {0,1} BY <9>1
                                        <12>9. Head(SecondElFromSeq(AtoB)) \in {0,1} BY  <9>5b, <12>5, HeadTailProperties  
                                        <12>10. Head(AtoB)[2] = Head(SecondElFromSeq(AtoB)) BY <9>8                                        
                                        <12>q QED BY <12>4, <12>6, <12>8, <12>9, <12>10, OrderPartitionConcatElem1LR2                                    
                                    <11>2. BVar[2] < AVar[2] BY <11>1, LesserTrans, <10>1, <9>1, <8>3a, <8>3b  
                                    <11>q QED BY <11>2
                                <10>2. CASE Head(AtoB)[2] < BVar[2]
                                    <11>1. Head(AtoB)[2] >= AVar[2]
                                        <12>1. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv
                                        <12>2. SecondElFromSeq(AtoB) = <<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) BY HeadTailPart, <9>5b, <12>1
                                        <12>3. Ordered2(SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                            <13>1. Ordered2(<<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>)) 
                                                <14>1. Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                                    <15>1. \/ Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB)  \o <<AVar[2]>>)  
                                                           \/ Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB)  \o <<AVar[2]>>) BY <8>2 DEF  Ordered  
                                                    <15>2. ASSUME Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB)  \o <<AVar[2]>>) PROVE FALSE
                                                        <16>1. Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB))
                                                            <17>1. <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF IndInv, TypeInv, SecondElFromSeq 
                                                            <17>2. <<AVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv 
                                                            <17>q QED BY OrderPartition1, <17>1, <17>2, <15>2
                                                        <16>2. Ordered1(<<BVar[2]>> \o (<<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)))) BY <12>2, <16>1
                                                        <16>3. Ordered1(<<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)))
                                                            <17>1. <<BVar[2]>> \o (<<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB))) =  <<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) 
                                                                <18>1. <<BVar[2]>> \in Seq({0, 1}) BY DEF IndInv, TypeInv, SecondElFromSeq 
                                                                <18>2. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                                                <18>3. <<Head(SecondElFromSeq(AtoB))>> \in Seq({0, 1}) BY <18>2 DEF IndInv, TypeInv, SecondElFromSeq 
                                                                <18>4. Tail(SecondElFromSeq(AtoB)) \in Seq({0, 1}) BY <18>2, <9>5b, HeadTailProperties 
                                                                <18>q QED BY ConcatAssociative, <18>1, <18>3, <18>4      
                                                            <17>q QED BY <17>1, <16>2                                                     
                                                        <16>4. Ordered1(<<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>>)
                                                            <17>2. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                                            <17>3. <<Head(SecondElFromSeq(AtoB))>> \in Seq({0, 1}) BY <17>2 DEF IndInv, TypeInv, SecondElFromSeq 
                                                            <17>4. Tail(SecondElFromSeq(AtoB)) \in Seq({0, 1}) BY <17>2, <9>5b, HeadTailProperties
                                                            <17>5. <<BVar[2]>> \o <<Head(SecondElFromSeq(AtoB))>> \in Seq({0, 1})  BY <17>3 DEF IndInv, TypeInv, SecondElFromSeq                                                                
                                                            <17>q QED BY OrderPartition1, <16>3, <17>5, <17>4
                                                        <16>5. Ordered1(<<BVar[2]>> \o << >> \o <<Head(SecondElFromSeq(AtoB))>>)
                                                            <17>1. <<BVar[2]>> \o << >> = <<BVar[2]>> BY ConcatEmptySeq, <9>3
                                                            <17>q QED BY <16>4, <17>1
                                                        <16>6. Head(SecondElFromSeq(AtoB)) >= BVar[2]
                                                            <17>1. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv                                                         
                                                            <17>2. <<BVar[2]>> \in  Seq({0,1}) BY DEF IndInv, TypeInv
                                                            <17>3. <<Head(SecondElFromSeq(AtoB))>> \in  Seq({0,1}) BY <17>1 DEF IndInv, TypeInv, SecondElFromSeq 
                                                            <17>q QED BY <16>5, OrderPartitionConcatElem1LR2, <17>2, <17>3
                                                        <16>7. Head(AtoB)[2] >= BVar[2] BY <16>6, <9>8
                                                        <16>q QED BY <16>7, <10>2, <9>1, <9>2, <9>3
                                                    <15>q QED BY <15>1, <15>2
                                                <14>2. <<BVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv 
                                                <14>3. <<AVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv   
                                                <14>4. SecondElFromSeq(AtoB) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq                                               
                                                <14>q QED BY <14>1,<14>2,<14>3,<14>4, ConcatAssociative
                                            <13>2. <<BVar[2]>> \in Seq({0,1}) BY DEF IndInv, TypeInv
                                            <13>4. (SecondElFromSeq(AtoB) \o <<AVar[2]>>) \in Seq({0,1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                            <13>q QED BY <13>1, <13>2, <13>4, OrderPartition2r
                                        <12>4. Ordered2(<<Head(SecondElFromSeq(AtoB))>> \o Tail(SecondElFromSeq(AtoB)) \o <<AVar[2]>>) BY <12>2, <12>3
                                        <12>5. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                        <12>6. Tail(SecondElFromSeq(AtoB)) \in Seq({0,1}) BY  <9>5b, <12>5, HeadTailProperties
                                        <12>8. AVar[2] \in {0,1} BY <9>1
                                        <12>9. Head(SecondElFromSeq(AtoB)) \in {0,1} BY  <9>5b, <12>5, HeadTailProperties  
                                        <12>10. Head(AtoB)[2] = Head(SecondElFromSeq(AtoB)) BY <9>8                                        
                                        <12>q QED BY <12>4, <12>6, <12>8, <12>9, <12>10, OrderPartitionConcatElem2LR2                                          
                                    <11>2. BVar[2] > AVar[2] BY <11>1, LesserTrans, <10>2, <9>1, <8>3a, <8>3b  
                                    <11>q QED BY <11>2                                
                                <10>q QED BY <10>1, <10>2, <9>1, <9>2, <8>6 
                            <9>6dddd. Head(AtoB)[2] = AVar[2] BY <8>6, <9>6d, <9>1, <9>2, <9>3                                 
                            <9>q QED BY <9>6dddd
                        <8>q QED BY <8>2, <8>4, <8>3, <8>6
                    <7>6. Head(AtoB) = AVar
                        <8>1. AtoB # << >> BY <4>4 DEF BRcv
                        <8>2. AtoB \in Seq(Data \X {0,1}) BY DEF IndInv, TypeInv   
                        <8>3. Len(AtoB) >= 1 BY EmptySeq, <8>1, <8>2
                        <8>q QED BY <7>2, <8>3 DEF IndInv, InvSend, Head                    
                    <7>q QED BY <7>1, <7>6
                <6>4. AVar[2] # BVar[2] 
                    <7>1. Ordered(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)  BY DEF IndInv, Toggle
                    <7>2. \/ Ordered1(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                          \/ Ordered2(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>) BY <7>1 DEF Ordered
                    <7>3. CASE Ordered1(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                        <8>4. Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                            <9>1. BtoA \o (<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>) = BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>
                                <10>1. BtoA \o (<<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>)) = BtoA \o <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                    <11>1. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>2. <<BVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>3. SecondElFromSeq(AtoB) \o <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                    <11>q QED BY <11>1, <11>2, <11>3, ConcatAssociative
                                <10>2. <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>) = <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>
                                    <11>1. <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>2. <<BVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>3. SecondElFromSeq(AtoB) \in Seq({0, 1})  BY DEF TypeInv, IndInv, SecondElFromSeq  
                                    <11>q QED BY <11>1, <11>2, <11>3, ConcatAssociative
                                <10>3. BtoA \o <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>) = BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>
                                    <11>1. BtoA \o <<BVar[2]>>  \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>2. <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>3. SecondElFromSeq(AtoB) \in Seq({0, 1})  BY DEF TypeInv, IndInv, SecondElFromSeq  
                                    <11>q QED BY <11>1, <11>2, <11>3, ConcatAssociative
                                <10>q QED BY ConcatAssociative, <10>1, <10>2,  <10>3
                            <9>2. Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                <10>1. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                <10>2. <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                <10>q QED BY OrderPartition1r, <7>3, <10>1, <10>2, <9>1 
                            <9>q QED BY <7>3, <9>1, <9>2                    
                        <8>2. Head(AtoB)[2] = Head(SecondElFromSeq(AtoB))
                            <9>1. AtoB \in Seq(Data \X {0,1}) BY DEF TypeInv, IndInv    
                            <9>2. AtoB # << >>  BY <4>4 DEF BRcv
                            <9>q QED BY SeqComm, <9>1, <9>2  
                        <8>1. Head(AtoB)[2] > BVar[2]
                            <9>1. Ordered1(<<BVar[2]>> \o SecondElFromSeq(AtoB))
                                <10>1. <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                <10>2. <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv  
                                <10>q QED BY <10>1, <10>2, OrderPartition1, <8>4
                            <9>2. \A i \in 1..Len(SecondElFromSeq(AtoB)) : SecondElFromSeq(AtoB)[i] >= BVar[2]
                                <10>1. BVar[2] \in {0, 1} BY DEF TypeInv, IndInv  
                                <10>2. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                                <10>q QED BY OrderPartitionConcatElem1L, <9>1, <10>1, <10>2
                            <9>3. SecondElFromSeq(AtoB)[1] >= BVar[2]
                                <10>2. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv
                                <10>3. Len(SecondElFromSeq(AtoB)) >= 1
                                    <11>1. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq 
                                    <11>q QED BY <11>1, <10>2, EmptySeq
                                <10>4. 1 \in 1..Len(SecondElFromSeq(AtoB)) BY <10>3
                                <10>q QED BY <10>4, <9>2
                            <9>4. Head(AtoB)[2] >= BVar[2] BY <9>3, <8>2
                            <9>q QED BY <9>4, <5>2
                        <8>3. Head(SecondElFromSeq(AtoB)) > BVar[2] BY <8>1, <8>2
                        <8>5. BVar[2] < AVar[2] 
                            <9>1. BVar[2] \in Nat BY DEF TypeInv, IndInv
                            <9>2. AVar[2] \in Nat BY DEF TypeInv, IndInv
                            <9>3. SecondElFromSeq(AtoB) \in Seq(Nat) BY DEF TypeInv, IndInv, SecondElFromSeq  
                            <9>4. \E i \in 1..Len(SecondElFromSeq(AtoB)): SecondElFromSeq(AtoB)[i] > BVar[2]
                                <10> SUFFICES ASSUME 1 \in 1..Len(SecondElFromSeq(AtoB))
                                     PROVE SecondElFromSeq(AtoB)[1] > BVar[2]
                                    <11>1. 1 \in 1..Len(SecondElFromSeq(AtoB)) 
                                        <12>1. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                        <12>2. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                        <12>3. Len(SecondElFromSeq(AtoB)) >= 1 BY <12>1, <12>2
                                        <12>q QED BY <12>3
                                    <11>q QED BY <11>1
                                <10>q QED BY <8>3
                            <9>q QED BY OrderPartition1MiddleR, <8>4, <9>1, <9>2, <9>3, <9>4
                        <8>q QED BY <8>5
                    <7>4. CASE Ordered2(BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                        <8>4. Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                            <9>1. BtoA \o (<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>) = BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>
                                <10>1. BtoA \o (<<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>)) = BtoA \o <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                    <11>1. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>2. <<BVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>3. SecondElFromSeq(AtoB) \o <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                    <11>q QED BY <11>1, <11>2, <11>3, ConcatAssociative
                                <10>2. <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>) = <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>
                                    <11>1. <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>2. <<BVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>3. SecondElFromSeq(AtoB) \in Seq({0, 1})  BY DEF TypeInv, IndInv, SecondElFromSeq  
                                    <11>q QED BY <11>1, <11>2, <11>3, ConcatAssociative
                                <10>3. BtoA \o <<BVar[2]>> \o (SecondElFromSeq(AtoB) \o <<AVar[2]>>) = BtoA \o <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>
                                    <11>1. BtoA \o <<BVar[2]>>  \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>2. <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                    <11>3. SecondElFromSeq(AtoB) \in Seq({0, 1})  BY DEF TypeInv, IndInv, SecondElFromSeq  
                                    <11>q QED BY <11>1, <11>2, <11>3, ConcatAssociative
                                <10>q QED BY ConcatAssociative, <10>1, <10>2,  <10>3
                            <9>2. Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>>)
                                <10>1. BtoA \in Seq({0, 1}) BY DEF TypeInv, IndInv
                                <10>2. <<BVar[2]>> \o SecondElFromSeq(AtoB) \o <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                <10>q QED BY OrderPartition2r, <7>4, <10>1, <10>2, <9>1 
                            <9>q QED BY <7>4, <9>1, <9>2                    
                        <8>2. Head(AtoB)[2] = Head(SecondElFromSeq(AtoB))
                            <9>1. AtoB \in Seq(Data \X {0,1}) BY DEF TypeInv, IndInv    
                            <9>2. AtoB # << >>  BY <4>4 DEF BRcv
                            <9>q QED BY SeqComm, <9>1, <9>2  
                        <8>1. Head(AtoB)[2] < BVar[2]
                            <9>1. Ordered2(<<BVar[2]>> \o SecondElFromSeq(AtoB))
                                <10>1. <<BVar[2]>> \o SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                <10>2. <<AVar[2]>> \in Seq({0, 1}) BY DEF TypeInv, IndInv  
                                <10>q QED BY <10>1, <10>2, OrderPartition2, <8>4
                            <9>2. \A i \in 1..Len(SecondElFromSeq(AtoB)) : SecondElFromSeq(AtoB)[i] <= BVar[2]
                                <10>1. BVar[2] \in {0, 1} BY DEF TypeInv, IndInv  
                                <10>2. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq
                                <10>q QED BY OrderPartitionConcatElem2L, <9>1, <10>1, <10>2
                            <9>3. SecondElFromSeq(AtoB)[1] <= BVar[2]
                                <10>2. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv
                                <10>3. Len(SecondElFromSeq(AtoB)) >= 1
                                    <11>1. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq 
                                    <11>q QED BY <11>1, <10>2, EmptySeq
                                <10>4. 1 \in 1..Len(SecondElFromSeq(AtoB)) BY <10>3
                                <10>q QED BY <10>4, <9>2
                            <9>4. Head(AtoB)[2] <= BVar[2] BY <9>3, <8>2
                            <9>q QED BY <9>4, <5>2
                        <8>3. Head(SecondElFromSeq(AtoB)) < BVar[2] BY <8>1, <8>2
                        <8>5. BVar[2] > AVar[2] 
                            <9>1. BVar[2] \in Nat BY DEF TypeInv, IndInv
                            <9>2. AVar[2] \in Nat BY DEF TypeInv, IndInv
                            <9>3. SecondElFromSeq(AtoB) \in Seq(Nat) BY DEF TypeInv, IndInv, SecondElFromSeq  
                            <9>4. \E i \in 1..Len(SecondElFromSeq(AtoB)): SecondElFromSeq(AtoB)[i] < BVar[2]
                                <10> SUFFICES ASSUME 1 \in 1..Len(SecondElFromSeq(AtoB))
                                     PROVE SecondElFromSeq(AtoB)[1] < BVar[2]
                                    <11>1. 1 \in 1..Len(SecondElFromSeq(AtoB)) 
                                        <12>1. SecondElFromSeq(AtoB) # << >>  BY <4>4 DEF BRcv, SecondElFromSeq, TypeInv, IndInv 
                                        <12>2. SecondElFromSeq(AtoB) \in Seq({0, 1}) BY DEF TypeInv, IndInv, SecondElFromSeq  
                                        <12>3. Len(SecondElFromSeq(AtoB)) >= 1 BY <12>1, <12>2
                                        <12>q QED BY <12>3
                                    <11>q QED BY <11>1
                                <10>q QED BY <8>3
                            <9>q QED BY OrderPartition2MiddleR, <8>4, <9>1, <9>2, <9>3, <9>4
                        <8>q QED BY <8>5                    
                    <7>q QED BY <7>2, <7>3, <7>4            
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
    <1>q QED BY <1>i, <1>1, <1>2, PTL DEF Spec, ABS!Spec
    

-----------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with fairness conditions added.                        *)
(***************************************************************************)
FairSpec == Spec  /\  SF_vars(ARcv) /\ SF_vars(BRcv) /\
                      WF_vars(ASnd) /\ WF_vars(BSnd)
=============================================================================
\* Modification History
\* Last modified Wed Mar 05 16:30:20 CET 2025 by appeltwi
\* Last modified Tue Dec 31 18:19:05 CET 2024 by appeltwi
\* Last modified Wed Dec 27 13:29:51 PST 2017 by lamport
\* Created Wed Mar 25 11:53:40 PDT 2015 by lamport
