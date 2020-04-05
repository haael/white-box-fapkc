# white-box-fapkc

White-Box Cryptography based on FAPKC algorithm

## What is FAPKC?

FAPKC stands for Finite Automata Public Key Cryptosystem. It is an algorithm developed by Tao Renji et al. That makes use of finite automata (Mealy machines). FAPKC contains RSA as a special instance.

## What is White-Box Cryptography?

This is a cryptographic grade program obfuscation. It allows a program to be obfuscated in such a way so it is impossible to disassemble, impossible to modify, but still possible to execute. Think of it as Trusted Computing in software.

## Can you use FAPKC to implement White-Box Cryptography?

Yes, and that what this project is about.

## Can any program be secured this way?

Only a program that can be represented as a finite automaton. In short, it is possible to add numbers and multiply by a constant, but multiplication is impossible. However it is possible to perform multiplication in a finite ring (i.e. 64 bits).

## What are the security guarantees of FAPKC?

Security of FAPKC is based on a hardness of factorizing compound finite automata, and the related problem of finding the automaton inverse.
If you have two automata F(x) and G(x), it is possible to create a composition of the automata: (F * G)(x) = F(G(x)). Now, given the composition F * G and one of the automata (for instance F) it is computationally hard to find the other automaton (in this case, G).
The related problem is finding the inverse automaton. Given the automaton performing function y = F(x) it is hard to find the automaton performing the inverse function x = F_inv(y).

## What are practical applications of White-Box Cryptography?

Limitless. For instance:
* payment cards, access cards, car keys
* securing firmware of IoT devices
* preventing critical parts of security software, such as antivirus programs, against modification
* safely storing secrets and private keys on a cloud
* DRM solutions

## What are the uses of White-Box Cryptography in blockchains?

You can use it as an alternative to Ethereum-style contract evaluation. In Ethereum, thousands of nodes execute the same code and then vote on the right result. With white-box cryptography only one node is neccessary to do the computations.
You can also use it to implement a "private virtual machine", where rules are enforced by the network, but the state of the contract is secret.

One exciting possibility is management of an external resource (like a bank account) by a trustless network.

## What is the state of the project?

This is an alpha version.

Algebraic modules are implemented, tested and working.

The first implementation of FAPKC0 is underway.

Production ready implementation of FAPKC3 is planned soon.

