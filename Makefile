# Makefile for CS322 HW3.
#
JFLAGS = -g
JC = javac

.SUFFIXES: .java .class

.java.class:
	$(JC) $(JFLAGS) $*.java

irint: 	ir/IR1.class ir/IR1Parser.class IR1Interp.class

clean:
	'rm' ir/*.class *.class


