#!/usr/bin/python3
#-*- coding:utf8 -*-

from jit_types import Compiler
from rings import BooleanRing
from automaton import automaton_factory
from pathlib import Path
import pickle


Automaton = automaton_factory(BooleanRing.get_algebra())
globals()[Automaton.__qualname__] = Automaton # make Automaton class picklable
Vector = Automaton.base_vector
const_Vector = Automaton.base_const_vector
Polynomial = Automaton.base_polynomial
Ring = Automaton.base_ring

zero = Ring.zero()
one = Ring.one()

memory_size = 2


def add(accumulator, addend):
	"Add the bit vector `addend` to the bit vector `accumulator` in place, interpreting them as integers."
	c = zero
	for n, (a, b) in enumerate(zip(iter(accumulator), iter(addend))):
		a = a.optimized()
		b = b.optimized()
		accumulator[n] = (a + b + c).optimized()
		c = (a * b | b * c | a * c).optimized()


def compare_eq(vec_a, vec_b):
	"Compare if the vectors are equal, returns one bit."
	r = zero
	for c in iter(vec_a + vec_b):
		r |= c.optimized()
		r = r.optimized()
	return r + one


def compare_lt(vec_a, vec_b):
	"Check if the bit vector `vec_a` is strictly smaller than `vec_b`, interpreting them as integers."
	a_wins = zero
	b_wins = zero
	#eq = zero
	for a, b in reversed(list(zip(iter(vec_a), iter(vec_b)))):
		a = a.optimized()
		b = b.optimized()
		a_wins |= (b_wins.optimized() + one) * a * (b + one)
		b_wins |= (a_wins.optimized() + one) * b * (a + one)
		#eq |= a + b
	return b_wins.optimized() #| (eq + one)


max_pwd_len = 16
def count_chars(input_stream, state, Vector):
	"Count certain types of characters in the provided password."
	
	# This function uses global variables `max_pwd_len` and `memory_size`.
	uppercase_letters, lowercase_letters, numeric_characters, special_characters, invalid_characters, countdown = state
	vec_1 = Vector(1, 8)
	vec_ms = Vector(memory_size * 4, 8)
	vec_pe = Vector(max_pwd_len + memory_size * 4, 8)
	
	for character in input_stream:
		begin_pos = compare_lt(countdown, vec_ms).optimized()
		middle_pos = (compare_lt(countdown, vec_pe) * (begin_pos + one)).optimized()
		
		x0, x1, x2, x3, x4, x5, x6, x7 = reversed(list(iter(character)))
		a_o = ((x3 + one) * (x4 | x5 | x6 | x7)).optimized()
		p_w = (x3 * (x4 + one)).optimized()
		x_z = (x3 * x4 * (x5 + one) * ((x6 + one) | (x7 + one))).optimized()
		uppercase_letter = ((x0 + one) * x1 * (x2 + one) * (a_o | p_w | x_z)).optimized()
		lowercase_letter = ((x0 + one) * x1 * x2 * (a_o | p_w | x_z)).optimized()
		numeric_character = zero
		special_character = zero
		invalid_character = zero
		
		add(uppercase_letters, middle_pos * uppercase_letter * vec_1)
		add(lowercase_letters, middle_pos * lowercase_letter * vec_1)
		add(numeric_characters, middle_pos * numeric_character * vec_1)
		add(special_characters, middle_pos * special_character * vec_1)
		add(invalid_characters, middle_pos * invalid_character * vec_1)
		add(countdown, vec_1)
		
		result = Vector(0, 8)
		add(result, begin_pos * countdown)
		add(result, begin_pos * character)
		add(result, begin_pos * Vector(137, 8))
		countdown_opt = countdown.optimized()
		result += compare_eq(countdown_opt, Vector(0 + max_pwd_len + memory_size * 4, 8)).optimized() * uppercase_letters.optimized()
		result += compare_eq(countdown_opt, Vector(1 + max_pwd_len + memory_size * 4, 8)).optimized() * lowercase_letters.optimized()
		result += compare_eq(countdown_opt, Vector(2 + max_pwd_len + memory_size * 4, 8)).optimized() * numeric_characters.optimized()
		result += compare_eq(countdown_opt, Vector(3 + max_pwd_len + memory_size * 4, 8)).optimized() * special_characters.optimized()
		result += compare_eq(countdown_opt, Vector(4 + max_pwd_len + memory_size * 4, 8)).optimized() * invalid_characters.optimized()
		
		yield result.optimized()


def lowercase(char, Vector):
	"Convert ASCII-encoded character to lowercase."
	x0, x1, x2, x3, x4, x5, x6, x7 = reversed(list(iter(char)))
	a_o = (x3 + one) * (x4 | x5 | x6 | x7)
	p_w = x3 * (x4 + one)
	x_z = x3 * x4 * (x5 + one) * ((x6 + one) | (x7 + one))
	big_letter = (x0 + one) * x1 * (x2 + one) * (a_o | p_w | x_z)
	return Vector(reversed([x0, x1, (x2 + big_letter), x3, x4, x5, x6, x7]))


def generate_keys():
	try:
		with Path('encrypt.pickle').open('rb') as f:
			encrypt = pickle.load(f)
		with Path('decrypt.pickle').open('rb') as f:
			decrypt = pickle.load(f)
	except (FileNotFoundError, EOFError):
		print()
		print("generating FAPKC0 automaton pair...")
		encrypt, decrypt = Automaton.fapkc0(block_size=8, memory_size=memory_size)
		print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
		print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
		print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
		print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
		
		print("optimization pass...")
		encrypt.optimize()
		decrypt.optimize()
		print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
		print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
		print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
		print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
		
		print("obfuscating states...")
		encrypt.mix_states()
		decrypt.mix_states()
		print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
		print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
		print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
		print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
		
		print("optimization pass...")
		encrypt.optimize()
		decrypt.optimize()
		print("encrypt automaton size", encrypt.output_transition.circuit_size(), encrypt.state_transition.circuit_size())
		print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
		print("decrypt automaton size", decrypt.output_transition.circuit_size(), decrypt.state_transition.circuit_size())
		print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
		
		with Path('encrypt.pickle').open('wb') as f:
			pickle.dump(encrypt, f)
		with Path('decrypt.pickle').open('wb') as f:
			pickle.dump(decrypt, f)
	
	return encrypt, decrypt


def test_functional_encryption():
	print()
	print(" ***")
	print("Testing functional encryption")
	print()
	print("bare generator test")
	state = [const_Vector.zero(8) for _i in range(6)]
	text = "12345678" + "ABCDabcdEFGHefgh" + "ABCD"
	print("text:\t", text)
	r = list(count_chars([const_Vector(ord(_ch), 8) for _ch in text], state, const_Vector))
	print("output:\t", ' '.join(['{:02x}'.format(int(_r)) for _r in r]))
	
	try:
		with Path('counting_automaton.pickle').open('rb') as f:
			counting_automaton = pickle.load(f)	
	except (FileNotFoundError, EOFError):
		print()
		print("synthesizing automaton from generator")
		
		state = [Vector([Automaton.s[1, 8 * _i + _j] for _j in range(8)]) for _i in range(6)]
		r = list(count_chars([Vector([Automaton.x[_i] for _i in range(8)])], state, Vector))
		for _r in r:
			output_transition = _r
		
		state_transition = []
		for _s in state:
			state_transition.extend(list(_s))
		state_transition = Vector(state_transition)
		
		counting_automaton = Automaton(output_transition, state_transition)
		print("counting automaton size", counting_automaton.output_transition.circuit_size(), counting_automaton.state_transition.circuit_size())
		#print("optimization pass")
		#counting_automaton.optimize()
		#print("counting automaton size", counting_automaton.output_transition.circuit_size(), counting_automaton.state_transition.circuit_size())
		
		with Path('counting_automaton.pickle').open('wb') as f:
			pickle.dump(counting_automaton, f)
	
	encrypt, decrypt = generate_keys()
	
	try:
		with Path('counting_homomorphic.pickle').open('rb') as f:
			counting_homomorphic = pickle.load(f)
	except (FileNotFoundError, EOFError):
		print()
		print("composing homomorphic automaton")
		counting_homomorphic = encrypt @ counting_automaton @ decrypt
		print("homomorphic automaton size", counting_homomorphic.output_transition.circuit_size(), counting_homomorphic.state_transition.circuit_size())
		
		print("optimization pass...")
		counting_homomorphic.optimize()
		print("homomorphic automaton size", counting_homomorphic.output_transition.circuit_size(), counting_homomorphic.state_transition.circuit_size())
		
		with Path('counting_homomorphic.pickle').open('wb') as f:
			pickle.dump(counting_homomorphic, f)
	
	print()
	print("properties")
	print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
	print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
	print("plain automaton component sizes:", [_c.circuit_size() for _c in counting_automaton.output_transition], [_c.circuit_size() for _c in counting_automaton.state_transition])
	print("homomorphic automaton component sizes:", [_c.circuit_size() for _c in counting_homomorphic.output_transition], [_c.circuit_size() for _c in counting_homomorphic.state_transition])		
	
	print()
	print("compiling automata...")
	compiler = Compiler()
	encrypt.compile('encrypt', compiler)
	decrypt.compile('decrypt', compiler)
	counting_automaton.compile('counting_automaton', compiler)
	counting_homomorphic.compile('counting_homomorphic', compiler)
	
	code = compiler.compile()
	encrypt_c = encrypt.wrap_compiled('encrypt', code)
	decrypt_c = decrypt.wrap_compiled('decrypt', code)
	counting_automaton_c = counting_automaton.wrap_compiled('counting_automaton', code)
	counting_homomorphic_c = counting_homomorphic.wrap_compiled('counting_homomorphic', code)
	
	with code:
		print()
		print("testing plain automaton")
		text = "12345678" + "ABCDabcdEFGHefgh" + "ABCD"
		print("text:\t\t", text)
		t = [const_Vector(ord(_ch), 8) for _ch in text]
		h = list(counting_automaton_c(t))
		print("output:\t\t", ' '.join(['{:02x}'.format(int(_h)) for _h in h]))
		
		print()
		print("testing FAPKC encryption/decryption")
		print("text:\t\t", text)
		e = list(encrypt_c(t))
		print("cipher:\t\t", ' '.join(['{:02x}'.format(int(_e)) for _e in e]))
		d = list(decrypt_c(e))
		print("decrypted:\t", ''.join([chr(int(_d)) for _d in d]))
		
		print()
		print("testing functional encryption")
		text = "123456" + "ABCDabcdEFGHefgh" + "ABCD7890"
		print("text:\t\t", text)
		t = [const_Vector(ord(_ch), 8) for _ch in text]
		e = list(encrypt_c(t))
		print("enc. input:\t", ' '.join(['{:02x}'.format(int(_e)) for _e in e]))
		r = list(counting_homomorphic_c(e))
		print("enc. output:\t", ' '.join(['{:02x}'.format(int(_r)) for _r in r]))
		d = list(decrypt_c(r))
		print("output:\t\t", ' '.join(['{:02x}'.format(int(_d)) for _d in d]))
	print()


def test_homomorphic_encryption():
	print()
	print(" ***")
	print("Testing homomorphic encryption")
	
	encrypt, decrypt = generate_keys()
	
	print("compiling automata...")
	compiler = Compiler()
	encrypt.compile('encrypt', compiler)
	decrypt.compile('decrypt', compiler)
	code1 = compiler.compile()
	
	encrypt_c = encrypt.wrap_compiled('encrypt', code1)
	decrypt_c = decrypt.wrap_compiled('decrypt', code1)
	
	print()
	print("testing FAPKC0 encryption / decryption")
	
	cleartext = "caller: Request direct Denver for Northwest Three Twenty-eight."
	print("text:\t\t", cleartext)
	
	cipher = [_r for _r in encrypt_c(const_Vector(ord(_ch), 8) for _ch in "%$" + cleartext + "!^")]
	
	#print("".join([chr(int(_r)) if 32 <= int(_r) <= 127 else '?' for _r in cipher]))
	
	print("cipher:\t\t", ' '.join(['{:02x}'.format(int(_c)) for _c in cipher]))
	text = "".join([chr(int(_r)) for _r in decrypt_c(cipher)][4:])
	print("decrypted:\t", text)
	
	try:
		with Path('lowercase_automaton.pickle').open('rb') as f:
			lowercase_automaton = pickle.load(f)
	except (FileNotFoundError, EOFError):
		print()
		print("synthesizing lowercase automaton")
		lowercase_automaton = Automaton(output_transition=lowercase(Vector(Automaton.x[_i] for _i in range(8)), Vector))
		print("lowercase automaton size:", lowercase_automaton.output_transition.circuit_size(), lowercase_automaton.state_transition.circuit_size())
		print("optimization pass...")
		lowercase_automaton.optimize()
		print("lowercase automaton size:", lowercase_automaton.output_transition.circuit_size(), lowercase_automaton.state_transition.circuit_size())
		
		with Path('lowercase_automaton.pickle').open('wb') as f:
			pickle.dump(lowercase_automaton, f)
	
	print()
	print("testing plain lowercase automaton")
	
	print("text:\t\t", cleartext)
	print("lowercase:\t", "".join([chr(int(_r)) for _r in lowercase_automaton(const_Vector(ord(_ch), 8) for _ch in cleartext)]))
	
	try:
		with Path('lowercase_homomorphic.pickle').open('rb') as f:
			lowercase_homomorphic = pickle.load(f)
	except (FileNotFoundError, EOFError):
		print()
		print("composing homomorphic automaton...")
		lowercase_homomorphic = encrypt @ lowercase_automaton @ decrypt
		print("homomorphic automaton size:", lowercase_homomorphic.output_transition.circuit_size(), lowercase_homomorphic.state_transition.circuit_size())
		#lowercase_homomorphic.mix_states()
		#print(lowercase_homomorphic.output_transition.circuit_size(), lowercase_homomorphic.state_transition.circuit_size())
		print("optimization pass...")
		lowercase_homomorphic.optimize()
		print("homomorphic automaton size:", lowercase_homomorphic.output_transition.circuit_size(), lowercase_homomorphic.state_transition.circuit_size())
		with Path('lowercase_homomorphic.pickle').open('wb') as f:
			pickle.dump(lowercase_homomorphic, f)
	
	print()
	print("properties")
	print("encryption automaton component sizes:", [_c.circuit_size() for _c in encrypt.output_transition], [_c.circuit_size() for _c in encrypt.state_transition])
	print("decryption automaton component sizes:", [_c.circuit_size() for _c in decrypt.output_transition], [_c.circuit_size() for _c in decrypt.state_transition])
	print("plain automaton component sizes:", [_c.circuit_size() for _c in lowercase_automaton.output_transition], [_c.circuit_size() for _c in lowercase_automaton.state_transition])
	print("homomorphic automaton component sizes:", [_c.circuit_size() for _c in lowercase_homomorphic.output_transition], [_c.circuit_size() for _c in lowercase_homomorphic.state_transition])		
	
	print()
	print("compiling automata...")
	compiler = Compiler()
	lowercase_homomorphic.compile('lowercase_homomorphic', compiler)
	code2 = compiler.compile()
	lowercase_homomorphic_c = lowercase_homomorphic.wrap_compiled('lowercase_homomorphic', code2)
	
	print()
	print("testing Gonzalez-Llamas homomorphic operations")
	
	print("text:\t\t\t", cleartext)
	with code1:
		cipher = [_r for _r in encrypt_c(const_Vector(ord(_ch), 8) for _ch in "A%$#" + cleartext + "!@^&")]
	print("cipher pre lowercase:\t", ' '.join(['{:02x}'.format(int(_c)) for _c in cipher]))
	with code2:
		lowercase_cipher = [_r for _r in lowercase_homomorphic_c(cipher)]
	print("cipher post lowercase:\t", ' '.join(['{:02x}'.format(int(_c)) for _c in lowercase_cipher]))
	with code1:
		text = "".join([chr(int(_r)) for _r in decrypt_c(lowercase_cipher)][8:])
	print("decrypted:\t\t", text)
	print()
	

if __name__ == '__main__':
	test_homomorphic_encryption()
	test_functional_encryption()


