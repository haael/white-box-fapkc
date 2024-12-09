#!/bin/sh

set -e

echo "utils"
./utils.py
echo

echo "fields"
./fields.py
echo

echo "vectors"
./vectors.py
echo

echo "operations"
./operations.py
echo

echo "polynomials"
./polynomials.py
echo

echo "machines"
./machines.py
echo

echo "memory"
./memory.py
echo

echo "tracing"
./tracing.py
echo

echo "optimized"
./optimized.py
echo

echo "AES"
./aes.py
echo

echo "FAPKC"
./fapkc.py
echo

