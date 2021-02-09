szmp8 is clone of kcpsm6(version:KCPSM6_Release9_30Sept14),szmp8 is base on verilog and behaver
difference from picobalze(kcpsm6): 1.read_strobe is aheade of one clk compare with kcmps6,so szmp8 can 
                                      read one port at one instruction cycle(2 clks)
                                   2.the interrupt can not be interrupt those instrution
                                      JUMP,JUMP Z(Z=1),JUMP NZ(Z=0),JUMP C(C=1),JUMP NC(C=0),JUMP@(sX,sY),                                    
                                      CALL,CALL Z(Z=1),CALL NZ(Z=0),CALL C(C=1),CALL NC(C=0),CALL@(sX,sY),
                                      RETURN,RETURN Z(Z=1),RETURN NZ(Z=0),RETURN C(C=1),RETURN NC(C=0),LOAD&RETURN sX,KK
                                   3.when an Interrupt Service Routine (ISR) is runing, the IE flag(when ISR is runing,IE=0) can not be changed by ENABLE INTERRUPT
                                      or DISABLE INTERRUPT, only can be changed with RETURNI ENABLE or RETURNI DISABLE
