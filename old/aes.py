#!/usr/bin/python3
#-*- coding:utf8 -*-


from pathlib import Path
import pickle
from collections import deque, Counter
from vec_types import Boolean, Integer, Array
from jit_types import Compiler
from rings import BooleanRing, RijndaelField
from automaton import automaton_factory
from utils import parallel

Automaton = automaton_factory(BooleanRing.get_algebra())
vector = Automaton.base_vector




def circular_shift(n, i):
	return ((n << i) & 0xff) | (n >> (8 - i))


def forward_sbox(x):
	y = RijndaelField(0x63)
	if x:
		x_inv = RijndaelField(x)**-1
		y += RijndaelField.sum(RijndaelField(circular_shift(int(x_inv), _i)) for _i in range(5))
	return int(y)


def inverse_sbox(y):
	x_inv = RijndaelField(0x5) + RijndaelField.sum(RijndaelField(circular_shift(int(y), _i)) for _i in (1, 3, 6))
	if x_inv:
		x = x_inv**-1
	else:
		x = x_inv
	return int(x)




try:
	with Path('aes-rcon.pickle').open('rb') as f:
		rcon = pickle.load(f)
except FileNotFoundError:
	print("Calculating AES round constants...")
	rf_2 = RijndaelField(2)
	rcon = Array([int(rf_2 ** _i) for _i in range(16)])
	with Path('aes-rcon.pickle').open('wb') as f:
		pickle.dump(rcon, f)


try:
	with Path('rf-mul2.pickle').open('rb') as f:
		rf_mul2 = pickle.load(f)
except FileNotFoundError:
	print("Calculating Rijndael multiplication by 2 circuit...")
	rf_2 = RijndaelField(2)
	rf_mul2 = Array([int(rf_2 * RijndaelField(_i)) for _i in range(256)])
	with Path('rf-mul2.pickle').open('wb') as f:
		pickle.dump(rf_mul2, f)


try:
	with Path('rf-mul3.pickle').open('rb') as f:
		rf_mul3 = pickle.load(f)
except FileNotFoundError:
	print("Calculating Rijndael multiplication by 3 circuit...")
	rf_3 = RijndaelField(3)
	rf_mul3 = Array([int(rf_3 * RijndaelField(_i)) for _i in range(256)])
	with Path('rf-mul3.pickle').open('wb') as f:
		pickle.dump(rf_mul3, f)


try:
	with Path('aes-sbox.pickle').open('rb') as f:
		sbox = pickle.load(f)
except FileNotFoundError:
	print("Calculating AES s-box...")
	sbox = Array(bytes(forward_sbox(_x) for _x in range(256)))
	with Path('aes-sbox.pickle').open('wb') as f:
		pickle.dump(sbox, f)


try:
	with Path('aes-rsbox.pickle').open('rb') as f:
		inv_sbox = pickle.load(f)
except FileNotFoundError:
	print("Calculating AES inverse s-box...")
	inv_sbox = Array(bytes(inverse_sbox(_x) for _x in range(256)))
	with Path('aes-rsbox.pickle').open('wb') as f:
		pickle.dump(inv_sbox, f)



def encrypt_sub_bytes(stream):
	"AES encrypt substitute bytes step. Delay 0, memory size 0, memory width 0."
	
	for input_ in stream:
		word = input_[0:8]
		counter = input_[8:18]
		
		#print(" sb", hex(int(word)), hex(int(counter)))
		
		#print("enter sb", word.circuit_size(), len(word.variables_set()), counter.circuit_size(), len(counter.variables_set()))

		rt = (Integer(counter) >> 6) & 0xf
		iword = Integer(word)
		output = (sbox[iword] * (rt < 10)) ^ (iword * (rt >= 10))
		#print("exit sb", output.i_value.circuit_size(), len(output.i_value.variables_set()), counter.circuit_size(), len(counter.variables_set()))
		yield output.i_value | counter


def encrypt_shift_rows(stream, history=deque([vector.zero(8)] * 24)):
	"AES encrypt shift rows step. Delay 12, memory size 24, memory width 8."
	
	permutation = Array([12, 8, 4, 0, 12, 8, 4, 16, 12, 8, 20, 16, 12, 24, 20, 16])
	
	for input_ in stream:
		word = input_[0:8]
		counter = input_[8:18]
		
		#print(" sr", hex(int(word)), hex(int(counter)))
		
		#print("enter sr", word.circuit_size(), len(word.variables_set()), counter.circuit_size(), len(counter.variables_set()))

		state = vector.zero(8)
		history.insert(0, state)
		
		while len(history) > 25:
			history.pop()
		
		counter = (Integer(counter) + (1024 - 12)) & 0x3ff
		
		c = counter & 0xf
		rt = (counter >> 6) & 0xf
		state[0:8] = word
		
		history_array = Array(history)
		
		output = (history_array[permutation[c]] * (rt < 10)) ^ (Integer(history[12]) * (rt >= 10))
		
		#print("exit sr", output.i_value.circuit_size(), len(output.i_value.variables_set()), counter.i_value.circuit_size(), len(counter.i_value.variables_set()))
		
		yield output.i_value | counter.i_value


def encrypt_mix_columns(stream, history=deque([vector.zero(8)] * 24)):
	"AES encrypt mix columns step. Delay 4, memory size 16, memory width 8."
	
	for input_ in stream:
		word = input_[0:8]
		counter = input_[8:18]
		
		#print(" mc", hex(int(word)), hex(int(counter)))
		
		#print("enter mc", word.circuit_size(), len(word.variables_set()), counter.circuit_size(), len(counter.variables_set()))
		
		state = vector.zero(8)
		history.insert(0, state)
		while len(history) > 25:
			history.pop()
		
		state[0:8] = word
		
		counter = (Integer(counter) + (1024 - 4)) & 0x3ff
		
		m = counter & 0x3
		rt = (counter >> 6) & 0xf
		
		h_1 = Integer(history[1][0:8])
		h_2 = Integer(history[2][0:8])
		h_3 = Integer(history[3][0:8])
		h_4 = Integer(history[4][0:8])
		h_5 = Integer(history[5][0:8])
		h_6 = Integer(history[6][0:8])
		h_7 = Integer(history[7][0:8])
		h_16 = Integer(history[16][0:8])
		
		#print(" mc history 0...7:", [_h.i_value.circuit_size() for _h in [h_1, h_2, h_3, h_4, h_5, h_6, h_7]])
		#print(" mc history 16:", h_16.i_value.circuit_size(), len(h_16.i_value.variables_set()))
		
		p = rf_mul2[h_4] ^ rf_mul3[h_3] ^ h_2 ^ h_1
		#print(" mc p", p.i_value.circuit_size(), len(p.i_value.variables_set()))
		q = h_5 ^ rf_mul2[h_4] ^ rf_mul3[h_3] ^ h_2
		#print(" mc q", q.i_value.circuit_size(), len(q.i_value.variables_set()))
		r = h_6 ^ h_5 ^ rf_mul2[h_4] ^ rf_mul3[h_3]
		#print(" mc r", r.i_value.circuit_size(), len(r.i_value.variables_set()))
		s = rf_mul3[h_7] ^ h_6 ^ h_5 ^ rf_mul2[h_4]
		#print(" mc s", s.i_value.circuit_size(), len(s.i_value.variables_set()))
		
		output = ((((m == 0) * p) ^ ((m == 1) * q) ^ ((m == 2) * r) ^ ((m == 3) * s)) * (rt < 9)) ^ (h_4 * (rt >= 9))
		
		#if m == 0:
		#	print("      ", hex(int(p)), "=", "2 ·", hex(int(h_4)), "+", "3 ·", hex(int(h_3)), "+", hex(int(h_2)), "+", hex(int(h_1)))
		#elif m == 1:
		#	print("      ", hex(int(q)), "=", hex(int(h_5)), "+", "2 ·", hex(int(h_4)), "+", "3 ·", hex(int(h_3)), "+", hex(int(h_2)))
		#elif m == 2:
		#	print("      ", hex(int(r)), "=", hex(int(h_6)), "+", hex(int(h_5)), "+", "2 ·", hex(int(h_4)), "+", "3 ·", hex(int(h_3)))
		#elif m == 3:
		#	print("      ", hex(int(s)), "=", "3 ·", hex(int(h_7)), "+", hex(int(h_6)), "+", hex(int(h_5)), "+", "2 ·", hex(int(h_4)))
		
		#print("exit mc", output.i_value.circuit_size(), len(output.i_value.variables_set()), counter.i_value.circuit_size(), len(counter.i_value.variables_set()))
		
		yield output.i_value | counter.i_value


def generate_clock(stream, history=deque([vector.zero(10)])):
	"Output 10-bit counter for use by other automata."
	
	for word in stream:
		state = vector.zero(10)
		history.insert(0, state)
		
		#print(" gc", hex(int(word)))
		
		while len(history) > 2:
			history.pop()
		
		counter = Integer(history[1][0:10])
		
		yield word | counter.i_value
		
		counter += 1
		counter &= 0x3ff
		state[0:10] = counter.i_value


def remove_clock(stream):
	for input_ in stream:
		output = input_[0:8]
		counter = input_[8:16]
		yield output



def delay(n, stream, history=deque([vector.zero(8)] * 16)):
	"Delayed identity automaton. Memory size and delay equal to the argument."
	
	for input_ in stream:
		word = input_[0:8]
		counter = input_[8:18]
		
		#print(" delay", n, hex(int(word)), hex(int(counter)))
		
		history.insert(0, word)
		while len(history) > n + 1:
			history.pop()
		
		yield history[n] | ((Integer(counter) + (1024 - n)) & 0x3ff).i_value



def exhaust(generator):
	try:
		next(generator)
	except StopIteration:
		pass
	else:
		raise RuntimeError


try:
	with Path('delay_16_fsm.pickle').open('rb') as f:
		delay_16_fsm = pickle.load(f)
except FileNotFoundError:
	print("Calculating delay by 16 automaton...")
	
	argument = vector(Automaton.x[_i] for _i in range(18))
	history = deque(vector(Automaton.s[_j, _i] for _i in range(8)) for _j in range(1, 17))
	generator = delay(16, [argument], history)
	result = next(generator)
	exhaust(generator)
	delay_16_fsm = Automaton(output_transition=result, state_transition=history[0])
	delay_16_fsm.optimize()
	
	with Path('delay_16_fsm.pickle').open('wb') as f:
		pickle.dump(delay_16_fsm, f)


try:
	with Path('generate_clock_fsm.pickle').open('rb') as f:
		generate_clock_fsm = pickle.load(f)
except FileNotFoundError:
	print("Calculating clock generator automaton...")
	
	argument = vector(Automaton.x[_i] for _i in range(8))
	history = deque(vector(Automaton.s[_j, _i] for _i in range(10)) for _j in range(1, 33))
	generator = generate_clock([argument], history)
	result = next(generator)
	exhaust(generator)
	generate_clock_fsm = Automaton(output_transition=result, state_transition=history[0])
	generate_clock_fsm.optimize()
	
	with Path('generate_clock_fsm.pickle').open('wb') as f:
		pickle.dump(generate_clock_fsm, f)


try:
	with Path('remove_clock_fsm.pickle').open('rb') as f:
		remove_clock_fsm = pickle.load(f)
except FileNotFoundError:
	print("Calculating clock removal automaton...")
	
	argument = vector(Automaton.x[_i] for _i in range(18))
	history = deque(vector(Automaton.s[_j, _i] for _i in range(0)) for _j in range(1, 2))
	generator = remove_clock([argument])
	result = next(generator)
	exhaust(generator)
	remove_clock_fsm = Automaton(output_transition=result, state_transition=history[0])
	remove_clock_fsm.optimize()
	
	with Path('remove_clock_fsm.pickle').open('wb') as f:
		pickle.dump(remove_clock_fsm, f)


try:
	with Path('encrypt_sub_bytes_fsm.pickle').open('rb') as f:
		encrypt_sub_bytes_fsm = pickle.load(f)
except FileNotFoundError:
	print("Calculating AES encrypt substitute bytes automaton...")
	
	argument = vector(Automaton.x[_i] for _i in range(18))
	history = deque(vector(Automaton.s[_j, _i] for _i in range(0)) for _j in range(1, 2))
	generator = encrypt_sub_bytes([argument])
	result = next(generator)
	exhaust(generator)
	encrypt_sub_bytes_fsm = Automaton(output_transition=result, state_transition=history[0])
	encrypt_sub_bytes_fsm.optimize()
	
	with Path('encrypt_sub_bytes_fsm.pickle').open('wb') as f:
		pickle.dump(encrypt_sub_bytes_fsm, f)


try:
	with Path('encrypt_shift_rows_fsm.pickle').open('rb') as f:
		encrypt_shift_rows_fsm = pickle.load(f)
except FileNotFoundError:
	print("Calculating AES encrypt shift rows automaton...")
	
	argument = vector(Automaton.x[_i] for _i in range(18))
	history = deque(vector(Automaton.s[_j, _i] for _i in range(8)) for _j in range(1, 25))
	generator = encrypt_shift_rows([argument], history)
	result = next(generator)
	exhaust(generator)
	encrypt_shift_rows_fsm = Automaton(output_transition=result, state_transition=history[0])
	encrypt_shift_rows_fsm.optimize()
	
	with Path('encrypt_shift_rows_fsm.pickle').open('wb') as f:
		pickle.dump(encrypt_shift_rows_fsm, f)


try:
	with Path('encrypt_mix_columns_fsm.pickle').open('rb') as f:
		encrypt_mix_columns_fsm = pickle.load(f)
except FileNotFoundError:
	print("Calculating AES encrypt mix columns automaton...")
	
	argument = vector(Automaton.x[_i] for _i in range(18))
	history = deque(vector(Automaton.s[_j, _i] for _i in range(8)) for _j in range(1, 27))
	generator = encrypt_mix_columns([argument], history)
	result = next(generator)
	exhaust(generator)
	encrypt_mix_columns_fsm = Automaton(output_transition=result, state_transition=history[0])
	encrypt_mix_columns_fsm.optimize()
	
	with Path('encrypt_mix_columns_fsm.pickle').open('wb') as f:
		pickle.dump(encrypt_mix_columns_fsm, f)








# delay 0
def add_round_key_128(key, stream, history=deque([vector.zero(8)] * 16)):
	key_array = Array(key)
	
	for input_ in stream:
		word = input_[0:8]
		counter = input_[8:18]
		
		#print(" ark", hex(int(word)), hex(int(counter)))
		
		#print("enter ark", word.circuit_size(), len(word.variables_set()), counter.circuit_size(), len(counter.variables_set()))

		state = vector.zero(8)
		history.insert(0, state)
		while len(history) > 17:
			history.pop()
		
		r = Integer(counter)
		rt = (r >> 6) & 0xf
		c = r & 0x3f
		
		near_item = Integer(0)
		near_item ^= (sbox[Integer(history[16 - 13])] ^ rcon[rt]) * (c == 3 * 16 + 0)
		near_item ^= sbox[Integer(history[16 - 13])] * ((c == 3 * 16 + 1) ^ (c == 3 * 16 + 2))
		near_item ^= sbox[Integer(history[16 - 9])] * (c == 3 * 16 + 3)
		near_item ^= Integer(history[16 - 12]) * (c >= 3 * 16 + 4)
		
		output = Integer(history[16]) ^ Integer(word)
		next_key = ((Integer(history[16]) ^ (near_item * (c >= 3 * 16))) * (r < 1024 - 16)) ^ (key_array[r & 0xf] * (r >= 1024 - 16))
		
		#print("exit ark", output.i_value.circuit_size(), len(output.i_value.variables_set()), counter.circuit_size(), len(counter.variables_set()))
		#print(" ark", str(counter), str(rt), str(rcon[rt]), str(c == 3 * 16 + 0), str(r), str(c), ":", str(word), "^", str(history[16]), "=", str(output))
		
		yield output.i_value | counter
		
		state[0:8] = next_key.i_value




def encrypt_aes_128(key, stream, history=deque([vector.zero(3 * 8 + 10 + 16)] * 64)): # debug -16
	rk_history = deque(_word[0:8] for _word in history)
	sr_history = deque(_word[8:16] for _word in history)
	mc_history = deque(_word[16:24] for _word in history)
	gc_history = deque(_word[24:34] for _word in history)
	di_history = deque(_word[34:42] for _word in history) # debug
	do_history = deque(_word[42:50] for _word in history) # debug
	
	stream = generate_clock(stream, gc_history)
	stream = delay(16, stream, di_history) # debug, delay 16
	stream = add_round_key_128(key, stream, rk_history)
	stream = encrypt_sub_bytes(stream)
	stream = encrypt_shift_rows(stream, sr_history) # delay 12
	stream = encrypt_mix_columns(stream, mc_history) # delay 4
	stream = delay(16, stream, do_history) # debug, delay 16
	
	for input_ in stream:
		output = input_[0:8]
		counter = input_[8:16]
		yield output
	
	for i in range(max(len(rk_history), len(sr_history), len(mc_history), len(gc_history), len(di_history), len(do_history))):
		if len(history) <= i:
			history.append(vector.zero(3 * 8 + 10 + 16)) # debug -16
		
		history[i] = (rk_history[i] if i < len(rk_history) else vector.zero(8)) | \
		             (sr_history[i] if i < len(sr_history) else vector.zero(8)) | \
		             (mc_history[i] if i < len(mc_history) else vector.zero(8)) | \
		             (gc_history[i] if i < len(gc_history) else vector.zero(10)) | \
		             (di_history[i] if i < len(di_history) else vector.zero(8)) | \
		             (do_history[i] if i < len(do_history) else vector.zero(8)) # debug
		
		if len(history) > max(len(rk_history), len(sr_history), len(mc_history), len(gc_history), len(di_history), len(do_history)):
			history.pop()



def test_encrypt_aes_128():
	key = bytes.fromhex('0f 47 0c af 15 d9 b7 7f 71 e8 ad 67 c9 59 d6 98')
	
	history = deque([vector.zero(32 + 10 + 16)] * 64)
	
	data_init = [None] * 4
	data_init[0] = [vector(_b, 8) for _b in bytes.fromhex('00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff')]
	data_init[1] = [vector(_b, 8) for _b in bytes.fromhex('34 9b a8 d2 43 97 8f e2 30 9a 30 98 48 0c d9 0a')]
	data_init[2] = [vector(_b, 8) for _b in bytes.fromhex('fe dc ba 98 76 54 32 10 fe dc ba 98 76 54 32 10')]
	data_init[3] = [vector(_b, 8) for _b in bytes.fromhex('39 48 7b cd 97 8d 13 29 84 3a 09 34 09 43 ab 5a')]
	
	for i in range(16*4):
		if i < 4:
			data = data_init[i]
		
		if i % 4 == 0:
			print()
			print(i // 4)
		
		print(' '.join(['{:02x}'.format(int(_k)) for _k in data]))
		data = list(encrypt_aes_128(key, data[:], history))



def generate_encrypt_aes_128_fsm(key):
	print("Composing AES round prefix automaton...")
	#print(" generate_clock:", [str(_x) for _x in generate_clock_fsm.output_transition], [str(_x) for _x in generate_clock_fsm.state_transition])
	#print(" delay 16:", [str(_x) for _x in delay_16_fsm.output_transition], [str(_x) for _x in delay_16_fsm.state_transition])
	
	aes_encrypt_round_prefix_fsm = generate_clock_fsm @ delay_16_fsm
	#print(" unoptimized:", [_x.circuit_size() for _x in aes_encrypt_round_prefix_fsm.output_transition], [_x.circuit_size() for _x in aes_encrypt_round_prefix_fsm.state_transition])
	aes_encrypt_round_prefix_fsm.optimize()
	#print(" optimized:", [str(_x) for _x in aes_encrypt_round_prefix_fsm.output_transition], [str(_x) for _x in aes_encrypt_round_prefix_fsm.state_transition])
	
	print("Composing AES round suffix automaton...")
	print(" sub_bytes:", [_x.circuit_size() for _x in encrypt_sub_bytes_fsm.output_transition], [_x.circuit_size() for _x in encrypt_sub_bytes_fsm.state_transition])
	print("           ", [len(_x.variables_set()) for _x in encrypt_sub_bytes_fsm.output_transition], [len(_x.variables_set()) for _x in encrypt_sub_bytes_fsm.state_transition])
	print(" shift_rows:", [_x.circuit_size() for _x in encrypt_shift_rows_fsm.output_transition], [_x.circuit_size() for _x in encrypt_shift_rows_fsm.state_transition])
	print("            ", [len(_x.variables_set()) for _x in encrypt_shift_rows_fsm.output_transition], [len(_x.variables_set()) for _x in encrypt_shift_rows_fsm.state_transition])
	print(" mix_columns:", [_x.circuit_size() for _x in encrypt_mix_columns_fsm.output_transition], [_x.circuit_size() for _x in encrypt_mix_columns_fsm.state_transition])
	print("             ", [len(_x.variables_set()) for _x in encrypt_mix_columns_fsm.output_transition], [len(_x.variables_set()) for _x in encrypt_mix_columns_fsm.state_transition])
	print(" delay_16:", [_x.circuit_size() for _x in delay_16_fsm.output_transition], [_x.circuit_size() for _x in delay_16_fsm.state_transition])
	print("          ", [len(_x.variables_set()) for _x in delay_16_fsm.output_transition], [len(_x.variables_set()) for _x in delay_16_fsm.state_transition])
	print(" remove_clock:", [_x.circuit_size() for _x in remove_clock_fsm.output_transition], [_x.circuit_size() for _x in remove_clock_fsm.state_transition])
	print("              ", [len(_x.variables_set()) for _x in remove_clock_fsm.output_transition], [len(_x.variables_set()) for _x in remove_clock_fsm.state_transition])
	
	with parallel():
		aes_encrypt_round_suffix_fsm = encrypt_sub_bytes_fsm @ encrypt_shift_rows_fsm @ encrypt_mix_columns_fsm @ delay_16_fsm @ remove_clock_fsm
		print(" unoptimized:", [_x.circuit_size() for _x in aes_encrypt_round_suffix_fsm.output_transition], [_x.circuit_size() for _x in aes_encrypt_round_suffix_fsm.state_transition])
		aes_encrypt_round_suffix_fsm.optimize()
		print(" optimized:", [_x.circuit_size() for _x in aes_encrypt_round_suffix_fsm.output_transition], [_x.circuit_size() for _x in aes_encrypt_round_suffix_fsm.state_transition])
		print(" ", [_x.circuit_size() for _x in aes_encrypt_round_suffix_fsm.output_transition], [_x.circuit_size() for _x in aes_encrypt_round_suffix_fsm.state_transition])
	
	print("Calculating AES 128 key automaton...")
	argument = vector(Automaton.x[_i] for _i in range(18))
	history = deque(vector(Automaton.s[_j, _i] for _i in range(8)) for _j in range(1, 17))
	generator = add_round_key_128(key, [argument], history)
	result = next(generator)
	exhaust(generator)
	add_round_key_128_fsm = Automaton(output_transition=result, state_transition=history[0])
	add_round_key_128_fsm.optimize()
	print(" ", [_x.circuit_size() for _x in add_round_key_128_fsm.output_transition], [_x.circuit_size() for _x in add_round_key_128_fsm.state_transition])
	
	print("Composing AES single round automaton...")
	encrypt_aes_128_fsm = aes_encrypt_round_prefix_fsm @ add_round_key_128_fsm @ aes_encrypt_round_suffix_fsm
	encrypt_aes_128_fsm.optimize()
	print(" ", [_x.circuit_size() for _x in encrypt_aes_128_fsm.output_transition], [_x.circuit_size() for _x in encrypt_aes_128_fsm.state_transition])


def test_encrypt_aes_128_fsm():
	key = bytes.fromhex('0f 47 0c af 15 d9 b7 7f 71 e8 ad 67 c9 59 d6 98')
	
	encrypt_aes_128_fsm = generate_encrypt_aes_128_fsm(key)
	
	history = deque([vector.zero(32 + 10 + 16)] * 64)
	
	data_init = [None] * 4
	data_init[0] = [vector(_b, 8) for _b in bytes.fromhex('00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff')]
	data_init[1] = [vector(_b, 8) for _b in bytes.fromhex('34 9b a8 d2 43 97 8f e2 30 9a 30 98 48 0c d9 0a')]
	data_init[2] = [vector(_b, 8) for _b in bytes.fromhex('fe dc ba 98 76 54 32 10 fe dc ba 98 76 54 32 10')]
	data_init[3] = [vector(_b, 8) for _b in bytes.fromhex('39 48 7b cd 97 8d 13 29 84 3a 09 34 09 43 ab 5a')]
	
	for i in range(16*4):
		if i < 4:
			data = data_init[i]
		
		if i % 4 == 0:
			print()
			print(i // 4)
		
		print(' '.join(['{:02x}'.format(int(_k)) for _k in data]))
		data = list(encrypt_aes_128_fsm(data[:], history))



if __debug__ and __name__ == '__main__':
	test_encrypt_aes_128_fsm()



quit()


	
print("Calculating AES circuit for key 1...")
	
argument = vector(Automaton.x[_i] for _i in range(8))
print(argument)
history = deque(vector(Automaton.s[_j, _i] for _i in range(32 + 10 + 16)) for _j in range(1, 65))
print()
for h in history:
	print(h)

print()

#with parallel():
print("calculating circuits")
result = list(encrypt_aes_128(key, [argument], history))[0]
print("creating automaton")
encrypt_aes_128_fsm = Automaton(output_transition=result, state_transition=history[0])


print()

for n, ot in enumerate(encrypt_aes_128_fsm.output_transition):
	print(hex(n), ot.circuit_size(), len(ot.variables_set()))

print()

for n, st in enumerate(encrypt_aes_128_fsm.state_transition):
	print(hex(n), st.circuit_size(), len(st.variables_set()))

print()

print("sizes:", encrypt_aes_128_fsm.output_transition.circuit_size(), encrypt_aes_128_fsm.state_transition.circuit_size(), len(encrypt_aes_128_fsm.state_transition))
compiler = Compiler()
encrypt_aes_128_fsm.compile('encrypt_aes_128', compiler)
code = compiler.compile()
encrypt_aes_128_fsm_c = encrypt_aes_128_fsm.wrap_compiled('encrypt_aes_128', code)






history = deque([vector.zero(32 + 10 + 16)] * 64)

data_init = [None] * 4
data_init[0] = [vector(_b, 8) for _b in bytes.fromhex('00 11 22 33 44 55 66 77 88 99 aa bb cc dd ee ff')]
data_init[1] = [vector(_b, 8) for _b in bytes.fromhex('34 9b a8 d2 43 97 8f e2 30 9a 30 98 48 0c d9 0a')]
data_init[2] = [vector(_b, 8) for _b in bytes.fromhex('fe dc ba 98 76 54 32 10 fe dc ba 98 76 54 32 10')]
data_init[3] = [vector(_b, 8) for _b in bytes.fromhex('39 48 7b cd 97 8d 13 29 84 3a 09 34 09 43 ab 5a')]


for i in range(16*4):
	if i < 4:
		data = data_init[i]
	
	if i % 4 == 0:
		print()
		print(i // 4)
		#print()
	print(' '.join(['{:02x}'.format(int(_k)) for _k in data]))
	data = list(encrypt_aes_128_fsm_c(data[:], history))
	#print("         >", ' '.join(['{:02x}'.format(int(_k)) for _k in data]))
	#print("", ' '.join(['{:010x}'.format(int(_k)) for _k in history]))

#suffix = [vector(0, 8) for _n in range(16)]
#data = list(encrypt_aes_128(key, suffix, history))
#print(' '.join(['{:02x}'.format(int(_k)) for _k in data]))

quit()

argument = vector(Automaton.x[_i] for _i in range(8))


#print(sbox[Integer(argument)])

#quit()


state = deque(vector(Automaton.s[_n, _i] for _i in range(8 * 16 + 12 + 12)) for _n in range(1, 17))

print(list(aes(0xeeeeee, [argument], state))[0])
print(state[0])

quit()



if __name__ == '__main__':	
	
	def sample_fn(input_stream, state=vector.zero(8 + 1)):
		uppercase = Boolean(state[0])
		lowercase = Boolean(state[1])
		numbers = Boolean(state[2])
		special = Boolean(state[3])
		length = Integer(state[4:8])
		
		min_pass_len = 3
		lower_a = ord('a')
		lower_z = ord('z')
		upper_a = ord('A')
		upper_z = ord('Z')
		char_0 = ord('0')
		char_9 = ord('9')
		
		for symbol in input_stream:
			assert len(symbol) <= 8
			char = Integer(symbol)
			
			lower_letter = (lower_a <= char) & (char <= lower_z)
			upper_letter = (upper_a <= char) & (char <= upper_z)
			digit = (char_0 <= char) & (char <= char_9)
			special_char = ~lower_letter & ~upper_letter & ~digit
			
			uppercase |= upper_letter
			lowercase |= lower_letter
			numbers |= digit
			special |= special_char
			length += (length < min_pass_len)
			length &= 0b1111
			
			#print(int(length))
			
			pass_ok = uppercase & lowercase & numbers & special & (length == min_pass_len)
			
			yield vector([pass_ok.b_value])
			
			assert length.bit_length() <= 4
		
		state[0] = uppercase.b_value
		state[1] = lowercase.b_value
		state[2] = numbers.b_value
		state[3] = special.b_value
		state[4:8] = length.i_value
	
	print("converting function to automaton")
	
	a = vector(ord('A'), 8)
	b = vector(ord('b'), 8)
	c = vector(ord(':'), 8)
	d = vector(ord('0'), 8)

	
	source_output = [int(x) for x in sample_fn([a, b, c, d])]
	print("source function output:", source_output)

	argument = vector(Automaton.x[_i] for _i in range(8))
	state = vector(Automaton.s[1, _i] for _i in range(9))
	result = list(sample_fn([argument], state))[0]
		
	sample_fsm = Automaton(output_transition=result, state_transition=state)
	fsm_output = [int(x) for x in sample_fsm([a, b, c, d])]
	print("plain automaton output:", fsm_output)
	
	assert source_output == fsm_output

	print("size of plain automaton:", sample_fsm.output_transition.circuit_size(), sample_fsm.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_fsm.state_transition])
	
	if __debug__: print("\n *** WARNING: try running the script with optimization flag `-O` to speed up obfuscated automaton generation ***\n")
	
	with parallel():
		print()
		print("obfuscating automaton")
		
		print("generating FAPKC keys")
		mixer8, unmixer8 = Automaton.fapkc0(block_size=8, memory_size=4)
		mixer1, unmixer1 = Automaton.fapkc0(block_size=1, memory_size=4)
		
		unmixer8.optimize()
		mixer1.optimize()
		
		sample_homo = mixer1 @ sample_fsm @ unmixer8
		print("size of raw homomorphic automaton:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
		sample_homo.optimize()
		print("after optimization:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
		sample_homo.mix_states()
		print("size of mixed homomorphic automaton:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
		sample_homo.optimize()
		print("after optimization:", sample_homo.output_transition.circuit_size(), sample_homo.state_transition.circuit_size(), [_c.circuit_size() for _c in sample_homo.state_transition])
	
	
	
	