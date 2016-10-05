#if 1== 2 then 3 else 4

li $t0 1
li $t1 2

bneq $t0 $t1 .else

.then:
#Code du then
 b .end
.else:
#Code du else
.end:
#Suide du code