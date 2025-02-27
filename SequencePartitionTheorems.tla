---------------------------- MODULE SequencePartitionTheorems ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, SequencesExt, SequenceTheorems, NaturalsInduction, SequencesExtTheorems

Ordered1(seq) == \A i, j \in 1..Len(seq) : i <= j => seq[i] <= seq[j]
Ordered2(seq) == \A i, j \in 1..Len(seq) : i <= j => seq[i] >= seq[j]

Ordered(seq) == \/ Ordered1(seq)
                \/ Ordered2(seq)
                
OrderProp1(seq1, seq2) == Ordered(seq1 \o seq2) => Ordered(seq1) /\ Ordered(seq1)

SecondElFromSeq(seq) == [i \in DOMAIN seq |-> seq[i][2]]      

THEOREM LesserTrans ==
    ASSUME NEW A \in Nat, NEW B \in Nat, NEW C \in Nat
    PROVE A <= B /\ B < C => A < C
        <1>q QED               
          <2> SUFFICES ASSUME A <= B /\ B < C
                       PROVE  A < C
            OBVIOUS
          <2>1. A < B \/ A = B OBVIOUS
          <2>2. CASE A < B BY DEF <
          <2>3. CASE A = B BY <2>3
          <2> QED BY <2>1, <2>2, <2>3

THEOREM OrderPartition ==
  ASSUME NEW S, NEW seq1 \in Seq(S), NEW seq2 \in Seq(S)
  PROVE  Ordered(seq1 \o seq2) => Ordered(seq1)
    <1>1. CASE Ordered1(seq1 \o seq2) BY <1>1 DEF Ordered, Ordered1
    <1>2. CASE Ordered2(seq1 \o seq2) BY <1>2 DEF Ordered, Ordered2
    <1>3. QED BY <1>1, <1>2 DEF Ordered
    
THEOREM OrderPartition1Middle ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW seq1 \in Seq(Nat), \E i \in 1..Len(seq1): seq1[i] < y
  PROVE  Ordered1(<<x>> \o seq1 \o <<y>>) => x < y      
  <1> SUFFICES ASSUME NEW i \in 1..Len(seq1),
                      seq1[i] < y,
                      Ordered1(<<x>> \o seq1 \o <<y>>)
               PROVE  x < y
    OBVIOUS
  <1>1. (<<x>> \o seq1 \o <<y>>)[1] = x BY ConcatProperties
  <1>2. (<<x>> \o seq1 \o <<y>>)[i + 1] = seq1[i] BY ConcatProperties  
  <1>3. i + 1 > 1 OBVIOUS
  <1>4. x <= seq1[i] BY <1>1, <1>2, <1>3 DEF Ordered1
  <1>6. x < y
    <2>1. seq1[i] \in Nat BY ElementOfSeq 
    <2>q QED BY LesserTrans, <1>4, <2>1
  <1>q QED BY <1>6
  
THEOREM OrderPartition2Middle ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW seq1 \in Seq(Nat), \E i \in 1..Len(seq1): seq1[i] > y
  PROVE  Ordered2(<<x>> \o seq1 \o <<y>>) => x > y      
  <1> SUFFICES ASSUME NEW i \in 1..Len(seq1),
                      seq1[i] > y,
                      Ordered2(<<x>> \o seq1 \o <<y>>)
               PROVE  x > y
    OBVIOUS
  <1>1. (<<x>> \o seq1 \o <<y>>)[1] = x BY ConcatProperties
  <1>2. (<<x>> \o seq1 \o <<y>>)[i + 1] = seq1[i] BY ConcatProperties  
  <1>3. i + 1 > 1 OBVIOUS
  <1>4. x >= seq1[i] BY <1>1, <1>2, <1>3 DEF Ordered2
  <1>6. x > y
    <2>1. seq1[i] \in Nat BY ElementOfSeq 
    <2>q QED BY LesserTrans, <1>4, <2>1
  <1>q QED BY <1>6  
  
THEOREM OrderPartition1MiddleR ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW seq1 \in Seq(Nat), \E i \in 1..Len(seq1): seq1[i] > x
  PROVE  Ordered1(<<x>> \o seq1 \o <<y>>) => x < y      
  <1> SUFFICES ASSUME NEW i \in 1..Len(seq1),
                      seq1[i] > x,
                      Ordered1(<<x>> \o seq1 \o <<y>>)
               PROVE  x < y
    OBVIOUS
  <1>1. (<<x>> \o seq1 \o <<y>>)[Len(<<x>> \o seq1 \o <<y>>)] = y BY ConcatProperties
  <1>2. (<<x>> \o seq1 \o <<y>>)[i + 1] = seq1[i] BY ConcatProperties  
  <1>3. i + 1 < Len(<<x>> \o seq1 \o <<y>>) OBVIOUS
  <1>4. y >= seq1[i] BY <1>1, <1>2, <1>3 DEF Ordered1
  <1>6. x < y
    <2>1. seq1[i] \in Nat BY ElementOfSeq 
    <2>q QED BY LesserTrans, <1>4, <2>1
  <1>q QED BY <1>6
  
THEOREM OrderPartition2MiddleR ==
  ASSUME NEW x \in Nat, NEW y \in Nat, NEW seq1 \in Seq(Nat), \E i \in 1..Len(seq1): seq1[i] < x
  PROVE  Ordered2(<<x>> \o seq1 \o <<y>>) => x > y      
  <1> SUFFICES ASSUME NEW i \in 1..Len(seq1),
                      seq1[i] < x,
                      Ordered2(<<x>> \o seq1 \o <<y>>)
               PROVE  x > y
    OBVIOUS
  <1>1. (<<x>> \o seq1 \o <<y>>)[Len(<<x>> \o seq1 \o <<y>>)] = y BY ConcatProperties
  <1>2. (<<x>> \o seq1 \o <<y>>)[i + 1] = seq1[i] BY ConcatProperties  
  <1>3. i + 1 < Len(<<x>> \o seq1 \o <<y>>) OBVIOUS
  <1>4. y <= seq1[i] BY <1>1, <1>2, <1>3 DEF Ordered2
  <1>6. x > y
    <2>1. seq1[i] \in Nat BY ElementOfSeq 
    <2>q QED BY LesserTrans, <1>4, <2>1
  <1>q QED BY <1>6      
   
    
THEOREM OrderPartition1 ==
  ASSUME NEW S, NEW seq1 \in Seq(S), NEW seq2 \in Seq(S)
  PROVE  Ordered1(seq1 \o seq2) => Ordered1(seq1)
    <1>3. QED BY DEF Ordered1   
    
THEOREM OrderPartition2 ==
  ASSUME NEW S, NEW seq1 \in Seq(S), NEW seq2 \in Seq(S)
  PROVE  Ordered2(seq1 \o seq2) => Ordered2(seq1)
    <1>3. QED BY DEF Ordered2  
      
    
THEOREM OrderPartition12 == 
    ASSUME NEW S, NEW seq \in Seq(S)
    PROVE Ordered2(Reverse(seq)) <=> Ordered1(seq) 
    <1>1. ASSUME Ordered2(Reverse(seq)) PROVE Ordered1(seq) 
        <2>1. \A i, j \in 1..Len(Reverse(seq)) : i <= j => Reverse(seq)[i] >= Reverse(seq)[j] BY <1>1 DEF Ordered2
        <2>2. \A i, j \in 1..Len(Reverse(seq)) : i <= j => seq[(Len(seq) - i)+1] >= seq[(Len(seq) - j)+1] BY <2>1 DEF Reverse
        <2>3. \A i, j \in 1..Len(seq) : i <= j => seq[(Len(seq) - i)+1] >= seq[(Len(seq) - j)+1] BY <2>2, ReverseProperties
        \* k = (Len(seq) - j)+1, l = (Len(seq) - i)+1
        <2>4. \A k, l \in 1..Len(seq) : k <= l => seq[k] <= seq[l]
          <3> SUFFICES ASSUME NEW k \in 1..Len(seq), NEW l \in 1..Len(seq),
                              k <= l
                       PROVE  seq[k] <= seq[l]
            OBVIOUS
          <3>1. ASSUME NEW j, j = (Len(seq) - k)+1, NEW i,  i = (Len(seq) - l)+1 PROVE  seq[(Len(seq) - i)+1] >= seq[(Len(seq) - j)+1]
            <4>1. i \in 1..Len(seq) BY <3>1
            <4>2. j \in 1..Len(seq) BY <3>1
            <4>3. i <= j  BY <3>1
            <4>q QED BY <2>3, <4>1, <4>2, <4>3
          <3>2. seq[k] <= seq[l] BY <3>1
          <3> QED BY <3>2
        <2>5. Ordered1(seq) BY <2>4 DEF Ordered1 
        <2>q QED BY <2>5, <1>1
    <1>2. ASSUME  Ordered1(seq) PROVE Ordered2(Reverse(seq)) 
        <2>1. \A k, l \in 1..Len(seq) : k <= l => seq[k] <= seq[l] BY <1>2 DEF Ordered1
        <2>2. \A k, l \in 1..Len(Reverse(seq)) : k <= l => seq[k] <= seq[l] 
            <3>1. Len(Reverse(seq)) = Len(seq) BY  ReverseProperties
            <3>q QED BY <3>1, <2>1    
        <2>3. \A i, j \in 1..Len(Reverse(seq)) : i <= j => seq[(Len(seq) - i)+1] >= seq[(Len(seq) - j)+1]
          <3> SUFFICES ASSUME NEW i \in 1..Len(Reverse(seq)), NEW j \in 1..Len(Reverse(seq)),
                              i <= j
                       PROVE  seq[(Len(seq) - i)+1] >= seq[(Len(seq) - j)+1]
            OBVIOUS
          <3>1. ASSUME NEW k, k = (Len(seq) - j)+1, NEW l,  l = (Len(seq) - i)+1 PROVE  seq[k] <= seq[l]
            <4>1. k \in 1..Len(seq) BY <3>1, ReverseProperties 
            <4>2. l \in 1..Len(seq) BY <3>1, ReverseProperties
            <4>3. k <= l  BY <3>1
            <4>q QED BY <2>1, <4>1, <4>2, <4>3      
          <3>2. seq[(Len(seq) - i)+1] >= seq[(Len(seq) - j)+1] BY <3>1    
          <3> QED BY <3>2
        <2>4. \A i, j \in 1..Len(Reverse(seq)) : i <= j => Reverse(seq)[i] >= Reverse(seq)[j] BY <2>3 DEF Reverse
        <2>5. Ordered2(Reverse(seq)) BY <2>4 DEF Ordered2
        <2>q QED BY <2>5, <1>2
    <1>q QED BY <1>1, <1>2    
        
    
THEOREM OrderPartition21== 
    ASSUME NEW S, NEW seq \in Seq(S)
    PROVE Ordered1(Reverse(seq)) = Ordered2(seq) 
    <1>q QED OBVIOUS   
    
THEOREM OrderPartition1r ==
  ASSUME NEW S, NEW seq1 \in Seq(S), NEW seq2 \in Seq(S)
  PROVE  Ordered1(seq1 \o seq2) => Ordered1(seq2)
    <1>1 Ordered2(Reverse(seq2)) = Ordered1(seq2) BY OrderPartition12
    <1>2 Ordered2(Reverse(seq2) \o Reverse(seq1)) => Ordered2(Reverse(seq2))
        <2>1. Reverse(seq2) \in Seq(S) BY DEF Reverse
        <2>2. Reverse(seq1) \in Seq(S) BY DEF Reverse
        <2>q QED BY <2>1, <2>2, OrderPartition2
    <1>3. Ordered1(Reverse(Reverse(seq2) \o Reverse(seq1))) = Ordered2(Reverse(seq2) \o Reverse(seq1))
        <2>1. Reverse(seq2) \o Reverse(seq1) \in Seq(S)
            <3>2. Reverse(seq2) \in Seq(S) BY DEF Reverse
            <3>3. Reverse(seq1) \in Seq(S) BY DEF Reverse        
            <3>q QED BY <3>2, <3>3, ConcatProperties        
        <2>q QED BY <2>1, OrderPartition21,  ReverseProperties  
    <1>4. Ordered1(seq1 \o seq2) = Ordered1(Reverse(Reverse(seq2) \o Reverse(seq1)))
        <2>1. Ordered1(Reverse(Reverse(seq2) \o Reverse(seq1)))  = Ordered1(Reverse(Reverse(seq1 \o seq2))) BY ReverseConcat
        <2>2. Ordered1(Reverse(Reverse(seq1 \o seq2))) = Ordered1(seq1 \o seq2) BY ReverseProperties
        <2>q QED BY <2>1, <2>2
    <1>q QED BY <1>1, <1>2, <1>3, <1>4 DEF Ordered1     
    
THEOREM OrderPartition2r ==
  ASSUME NEW S, NEW seq1 \in Seq(S), NEW seq2 \in Seq(S)
  PROVE  Ordered2(seq1 \o seq2) => Ordered2(seq2)
    <1>1 Ordered1(Reverse(seq2)) = Ordered2(seq2) BY OrderPartition21
    <1>2 Ordered1(Reverse(seq2) \o Reverse(seq1)) => Ordered1(Reverse(seq2))
        <2>1. Reverse(seq2) \in Seq(S) BY DEF Reverse
        <2>2. Reverse(seq1) \in Seq(S) BY DEF Reverse
        <2>q QED BY <2>1, <2>2, OrderPartition1
    <1>3. Ordered2(Reverse(Reverse(seq2) \o Reverse(seq1))) = Ordered1(Reverse(seq2) \o Reverse(seq1))
        <2>1. Reverse(seq2) \o Reverse(seq1) \in Seq(S)
            <3>2. Reverse(seq2) \in Seq(S) BY DEF Reverse
            <3>3. Reverse(seq1) \in Seq(S) BY DEF Reverse        
            <3>q QED BY <3>2, <3>3, ConcatProperties
        <2>q QED BY <2>1, OrderPartition12,  ReverseProperties  
    <1>4. Ordered2(seq1 \o seq2) = Ordered2(Reverse(Reverse(seq2) \o Reverse(seq1)))
        <2>1. Ordered2(Reverse(Reverse(seq2) \o Reverse(seq1)))= Ordered2(Reverse(Reverse(seq1 \o seq2))) BY ReverseConcat
        <2>2. Ordered2(Reverse(Reverse(seq1 \o seq2))) = Ordered2(seq1 \o seq2) BY ReverseProperties
        <2>q QED BY <2>1, <2>2
    <1>q QED BY <1>1, <1>2, <1>3, <1>4 DEF Ordered1         
    
THEOREM OrderPartitionr ==
  ASSUME NEW S, NEW seq1 \in Seq(S), NEW seq2 \in Seq(S)
  PROVE  Ordered(seq1 \o seq2) => Ordered(seq2)    
    <1>1. CASE Ordered1(seq1 \o seq2) BY <1>1, OrderPartition1r DEF Ordered, Ordered1
    <1>2. CASE Ordered2(seq1 \o seq2) BY <1>2, OrderPartition2r DEF Ordered, Ordered2
    <1>3. QED BY <1>1, <1>2 DEF Ordered  
    
THEOREM SingletonSeqInSeq ==
    ASSUME NEW P, NEW x \in P
    PROVE <<x>> \in Seq(P)
    BY DEF Seq  
     
  
THEOREM OrderTrans == 
    ASSUME NEW a \in Nat, NEW b \in Nat, NEW c \in Nat, a <= b /\ b <= c
               PROVE a <= c  
    OBVIOUS     
    
THEOREM OrderPartitionConcatElem1R ==
  ASSUME NEW S, NEW x \in S, NEW seq1 \in Seq(S),  seq1 # <<>>
  PROVE  Ordered1(seq1 \o <<x>>) => \A i \in 1..Len(seq1): seq1[i] <= x       
  <1> SUFFICES ASSUME Ordered1(seq1 \o <<x>>),
                      NEW i \in 1..Len(seq1)
               PROVE  seq1[i] <= x
    OBVIOUS
  <1>1. <<x>> \in Seq(S) BY SingletonSeqInSeq
  <1>12. (seq1 \o <<x>>)[Len(seq1 \o <<x>>)] = x BY <1>1, ConcatProperties
  <1>13. Len(seq1) < Len(seq1 \o <<x>>) BY <1>1, ConcatProperties
  <1>14. i <= Len(seq1) OBVIOUS
  <1>15. i < Len(seq1 \o <<x>>) BY <1>13, <1>14
  <1>16. seq1[i] <= x BY <1>15, <1>12 DEF Ordered1 
  <1>q QED BY <1>16
  
THEOREM OrderPartitionConcatElem2R ==
  ASSUME NEW S, NEW x \in S, NEW seq1 \in Seq(S),  seq1 # <<>>
  PROVE  Ordered2(seq1 \o <<x>>) => \A i \in 1..Len(seq1): seq1[i] >= x       
  <1> SUFFICES ASSUME Ordered2(seq1 \o <<x>>),
                      NEW i \in 1..Len(seq1)
               PROVE  seq1[i] >= x
    OBVIOUS
  <1>1. <<x>> \in Seq(S) BY SingletonSeqInSeq
  <1>12. (seq1 \o <<x>>)[Len(seq1 \o <<x>>)] = x BY <1>1, ConcatProperties
  <1>13. Len(seq1) < Len(seq1 \o <<x>>) BY <1>1, ConcatProperties
  <1>14. i <= Len(seq1) OBVIOUS
  <1>15. i < Len(seq1 \o <<x>>) BY <1>13, <1>14
  <1>16. seq1[i] >= x BY <1>15, <1>12 DEF Ordered2
  <1>q QED BY <1>16  
  
THEOREM OrderPartitionConcatElem1L ==
  ASSUME NEW S, NEW x \in S, NEW seq1 \in Seq(S),  seq1 # <<>>
  PROVE  Ordered1(<<x>> \o seq1) => \A i \in 1..Len(seq1): seq1[i] >= x       
  <1> SUFFICES ASSUME Ordered1(<<x>> \o seq1),
                      NEW i \in 1..Len(seq1)
               PROVE  seq1[i] >= x
    OBVIOUS
  <1>1. <<x>> \in Seq(S) BY SingletonSeqInSeq
  <1>12. (<<x>> \o seq1)[1] = x BY <1>1, ConcatProperties
  <1>13. Len(seq1) < Len(<<x>> \o seq1) BY <1>1, ConcatProperties
  <1>14. (<<x>> \o seq1)[i + 1] = seq1[i] BY <1>1, ConcatProperties  
  <1>16. seq1[i] >= x BY <1>12, <1>14 DEF Ordered1 
  <1>q QED BY <1>16  
  
 THEOREM OrderPartitionConcatElem1LR ==
  ASSUME NEW S, NEW x \in S, NEW y \in S, NEW seq1 \in Seq(S), seq1 # <<>>
  PROVE  Ordered1(<<x>> \o seq1 \o <<y>>) => \A i \in 1..Len(seq1): /\ x <= seq1[i] 
                                                                    /\ seq1[i]  <= y
                                                                    /\ x <= y
   <1> SUFFICES ASSUME Ordered1(<<x>> \o seq1 \o <<y>>),
                       NEW i \in 1..Len(seq1)
                PROVE  /\ x <= seq1[i] 
                       /\ seq1[i]  <= y
                       /\ x <= y
     OBVIOUS
  <1>1. <<x>> \in Seq(S) BY SingletonSeqInSeq
  <1>2. <<y>> \in Seq(S) BY SingletonSeqInSeq 
  <1>3. 1 <  Len(<<x>> \o seq1 \o <<y>>) OBVIOUS
  <1>11. (<<x>> \o seq1 \o <<y>>)[Len(<<x>> \o seq1 \o <<y>>)] = y BY <1>1, ConcatProperties  
  <1>12. (<<x>> \o seq1 \o <<y>>)[1] = x BY <1>1, ConcatProperties
  <1>13. Len(seq1) < Len(<<x>> \o seq1 \o <<y>>) BY <1>1, ConcatProperties
  <1>14. (<<x>> \o seq1 \o <<y>>)[i + 1] = seq1[i] BY <1>1, ConcatProperties  
  <1>15. i < Len(<<x>> \o seq1 \o <<y>>) BY <1>13, <1>14  
  <1>16. seq1[i] >= x BY <1>12, <1>14 DEF Ordered1 
  <1>17. seq1[i] <= y BY <1>15, <1>11, <1>14 DEF Ordered1 
  <1>18. x <= y BY <1>11, <1>12, <1>3 DEF Ordered1
  <1>q QED BY <1>16, <1>17, <1>18  
  
 THEOREM OrderPartitionConcatElem1LR2 ==
  ASSUME NEW S, NEW x \in S, NEW y \in S, NEW seq1 \in Seq(S)
  PROVE  Ordered1(<<x>> \o seq1 \o <<y>>) => x <= y
   <1> SUFFICES ASSUME Ordered1(<<x>> \o seq1 \o <<y>>)
                PROVE  x <= y
     OBVIOUS
   <1>1. <<x>> \in Seq(S) BY SingletonSeqInSeq
   <1>2. <<y>> \in Seq(S) BY SingletonSeqInSeq      
   <1>3. 1 <  Len(<<x>> \o seq1 \o <<y>>) OBVIOUS  
   <1>11. (<<x>> \o seq1 \o <<y>>)[Len(<<x>> \o seq1 \o <<y>>)] = y BY <1>1, ConcatProperties  
   <1>12. (<<x>> \o seq1 \o <<y>>)[1] = x BY <1>1, ConcatProperties
   <1>18. x <= y BY <1>11, <1>12, <1>3 DEF Ordered1
   <1>q QED BY <1>18
   
THEOREM OrderPartitionConcatElem2LR2 ==
  ASSUME NEW S, NEW x \in S, NEW y \in S, NEW seq1 \in Seq(S)
  PROVE  Ordered2(<<x>> \o seq1 \o <<y>>) => x >= y
   <1> SUFFICES ASSUME Ordered2(<<x>> \o seq1 \o <<y>>)
                PROVE  x >= y
     OBVIOUS
   <1>1. <<x>> \in Seq(S) BY SingletonSeqInSeq
   <1>2. <<y>> \in Seq(S) BY SingletonSeqInSeq      
   <1>3. 1 <  Len(<<x>> \o seq1 \o <<y>>) OBVIOUS  
   <1>11. (<<x>> \o seq1 \o <<y>>)[Len(<<x>> \o seq1 \o <<y>>)] = y BY <1>1, ConcatProperties  
   <1>12. (<<x>> \o seq1 \o <<y>>)[1] = x BY <1>1, ConcatProperties
   <1>18. x >= y BY <1>11, <1>12, <1>3 DEF Ordered2
   <1>q QED BY <1>18   
  
THEOREM OrderPartitionConcatElem2L ==
  ASSUME NEW S, NEW x \in S, NEW seq1 \in Seq(S),  seq1 # <<>>
  PROVE  Ordered2(<<x>> \o seq1) => \A i \in 1..Len(seq1): seq1[i] <= x       
  <1> SUFFICES ASSUME Ordered2(<<x>> \o seq1),
                      NEW i \in 1..Len(seq1)
               PROVE  seq1[i] <= x
    OBVIOUS
  <1>1. <<x>> \in Seq(S) BY SingletonSeqInSeq
  <1>12. (<<x>> \o seq1)[1] = x BY <1>1, ConcatProperties
  <1>13. Len(seq1) < Len(<<x>> \o seq1) BY <1>1, ConcatProperties
  <1>14. (<<x>> \o seq1)[i + 1] = seq1[i] BY <1>1, ConcatProperties  
  <1>16. seq1[i] <= x BY <1>12, <1>14 DEF Ordered2 
  <1>q QED BY <1>16   

THEOREM SeqComm ==
  ASSUME NEW S, NEW P, NEW seq \in Seq(S \X P),  seq # <<>>
  PROVE Head(seq)[2] = Head(SecondElFromSeq(seq)) BY DEF SecondElFromSeq
      
THEOREM FirstInSet ==
    ASSUME NEW S, NEW seq \in Seq(S), seq # <<>>
    PROVE seq[1] \in S
        <1>1. 1 \in 1..Len(seq) OBVIOUS
        <1>2. seq \in Seq(S) OBVIOUS
        <1>q QED BY <1>1, <1>2, ElementOfSeq
        
THEOREM HeadInSet ==
    ASSUME NEW S, NEW seq \in Seq(S), seq # <<>>
    PROVE Head(seq) \in S
        <1>1. 1 \in 1..Len(seq) OBVIOUS
        <1>2. seq \in Seq(S) OBVIOUS
        <1>q QED BY <1>1, <1>2, ElementOfSeq 
        
THEOREM HeadTailPart ==
    ASSUME NEW S, NEW seq \in Seq(S), seq # <<>>
    PROVE <<Head(seq)>> \o Tail(seq) = seq      
        <1>q QED BY DEF Head, Tail, Seq, \o 
        
=============================================================================
