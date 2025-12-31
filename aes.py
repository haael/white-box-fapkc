#!/usr/bin/python3


"AES cipher implementation, suitable for tracing."


__all__ = [
	'Rijndael',
	's_box_forward', 's_box_backward',
	'shift_rows_forward', 'shift_rows_backward',
	'mix_columns_forward', 'mix_columns_backward',
	'aes_encrypt_round', 'aes_decrypt_round',
	'key_schedule_128_forward', 'key_schedule_128_backward',
	'aes_128_encrypt', 'aes_128_decrypt'
]


from fields import Galois
from vectors import Vector
from copy import deepcopy


class Rijndael(Galois('Rijndael', 2, [1, 0, 0, 0, 1, 1, 0, 1, 1])):
	"Rijndael field."
	
	def __lshift_1(self):
		"Circular shift left by 1 bit in Rijndael field."
		
		if self._BinaryGalois__value < 0x80:
			return self * self.Field(0x02)
		else:
			return self.Field(0x02) * (self - self.Field(0x80)) + self.Field(0x01)
	
	def __lshift__(self, n):
		"Circular shift left by `n` bits in Rijndael field."
		
		x = self
		for m in range(n):
			x = x.__lshift_1()
		return x


def s_box_forward(x):
	"AES s-box."
	
	y = x**-1 if x else x.Field(0x00)
	return y + (y << 1) + (y << 2) + (y << 3) + (y << 4) + x.Field(0x63)


def s_box_backward(y):
	"Inverse AES s-box."
	
	x = (y << 1) + (y << 3) + (y << 6) + y.Field(0x05)
	return x**-1 if x else y.Field(0x00)


def shift_rows_forward(state):
	"Shift rows step of AES."
	
	values = [None] * 16
	for m in range(4):
		for n in range(4):
			values[4 * m + n] = state[4 * ((m + n) % 4) + n]
	return state.__class__(state.Array(values, [16, state.Field.field_bytesize], [state.Field]))


def shift_rows_backward(state):
	"Inverse shift rows step of AES."
	
	values = [None] * 16
	for m in range(4):
		for n in range(4):
			values[4 * m + n] = state[4 * ((m - n) % 4) + n]
	return state.__class__(state.Array(values, [16, state.Field.field_bytesize], [state.Field]))


def mix_columns_forward(state):
	"Mix columns step of AES."
	
	values = [None] * 16
	Field = state.Field
	_1 = Field(1)
	_2 = Field(2)
	_3 = Field(3)
	for m in range(4):
		b0 = state[4 * m + 0]
		b1 = state[4 * m + 1]
		b2 = state[4 * m + 2]
		b3 = state[4 * m + 3]
		values[4 * m + 0] = _2 * b0 + _3 * b1 + _1 * b2 + _1 * b3
		values[4 * m + 1] = _1 * b0 + _2 * b1 + _3 * b2 + _1 * b3
		values[4 * m + 2] = _1 * b0 + _1 * b1 + _2 * b2 + _3 * b3
		values[4 * m + 3] = _3 * b0 + _1 * b1 + _1 * b2 + _2 * b3
	return state.__class__(state.Array(values, [16, state.Field.field_bytesize], [Field]))


def mix_columns_backward(state):
	"Inverse mix columns step of AES."
	
	values = [None] * 16
	Field = state.Field
	_9 = Field(9)
	_11 = Field(11)
	_13 = Field(13)
	_14 = Field(14)
	for m in range(4):
		b0 = state[4 * m + 0]
		b1 = state[4 * m + 1]
		b2 = state[4 * m + 2]
		b3 = state[4 * m + 3]
		values[4 * m + 0] = _14 * b0 + _11 * b1 + _13 * b2 +  _9 * b3
		values[4 * m + 1] =  _9 * b0 + _14 * b1 + _11 * b2 + _13 * b3
		values[4 * m + 2] = _13 * b0 +  _9 * b1 + _14 * b2 + _11 * b3
		values[4 * m + 3] = _11 * b0 + _13 * b1 +  _9 * b2 + _14 * b3
	return state.__class__(state.Array(values, [16, state.Field.field_bytesize], [Field]))


def aes_encrypt_round(state):
	"Bit operations of AES encryption round."
	
	state = state.__class__(state.Array([s_box_forward(_word) for _word in state], [16, state.Field.field_bytesize], [state.Field]))
	state = shift_rows_forward(state)
	state = mix_columns_forward(state)
	return state


def aes_decrypt_round(state):
	"Bit operations of AES decryption round."
	
	state = mix_columns_backward(state)
	state = shift_rows_backward(state)
	state = state.__class__(state.Array([s_box_backward(_word) for _word in state], [16, state.Field.field_bytesize], [state.Field]))
	return state


def key_schedule_128_forward(state):
	"Outputs AES-128 key schedule. Modifies the key in place, so in the end it will be equal to the last (11th) round key."
	
	_2 = state.Field(2)
	
	yield deepcopy(state)
	
	for n in range(10):
		l = [_x for _x in state[12:16]]
		l = [s_box_forward(_x) for _x in l]
		l0 = l[0]
		del l[0]
		l.append(l0)
		l[0] += _2 ** n
		
		state[0:4] += state.__class__(state.Array(l, [4, state.Field.field_bytesize], [state.Field]))
		state[4:8] += state[0:4]
		state[8:12] += state[4:8]
		state[12:16] += state[8:12]
		
		yield deepcopy(state)


def key_schedule_128_backward(state):
	"Outputs AES-128 key schedule in reverse order. Expects the round key from the last (11th) round. Modifies the key in place, recovering the original key."
	
	_2 = state.Field(2)
	
	yield deepcopy(state)
	
	for n in reversed(range(10)):
		state[12:16] -= state[8:12]
		state[8:12] -= state[4:8]
		state[4:8] -= state[0:4]
		
		l = [_x for _x in state[12:16]]
		l = [s_box_forward(_x) for _x in l]
		l0 = l[0]
		del l[0]
		l.append(l0)
		l[0] += _2 ** n
		
		state[0:4] -= state.__class__(state.Array(l, [4, state.Field.field_bytesize], [state.Field]))
		
		yield deepcopy(state)


def aes_128_encrypt(forward_key, data):
	"AES-128 encryption. Modifies the key in place, so in the end it will be equal to the last round key."
	
	data = deepcopy(data)
	for n, round_key in enumerate(key_schedule_128_forward(forward_key)):
		data += round_key
		if n != 10:
			data = aes_encrypt_round(data)
		if n == 9:
			data = mix_columns_backward(data) # undo mix_columns
	return data


def aes_128_decrypt(backward_key, data):
	"AES-128 decryption. Expects key from last encryption round. Modifies the key in place, so in the end it will be equal to the original key."
	
	data = deepcopy(data)
	for n, round_key in enumerate(key_schedule_128_backward(backward_key)):
		data -= round_key
		if n == 0:
			data = mix_columns_forward(data) # undo mix_columns
		if n != 10:
			data = aes_decrypt_round(data)
	return data


if __debug__ and __name__ == '__main__':
	from random import randrange
	from memory import Array
	#Array = list
	
	_0 = Rijndael(0)
	_1 = Rijndael(1)
	_2 = Rijndael(2)
	assert _2 * (_1 / _2) == _1
	assert _2 * (_2**-1) == _1
	
	for x in Rijndael.domain():
		if x:
			assert _1 / x ==  x**-1
		assert s_box_backward(s_box_forward(x)) == x
		assert s_box_forward(s_box_backward(x)) == x
	
	for m in range(100):
		state = Vector.random(16, Array, Rijndael, randrange)
		
		assert shift_rows_backward(shift_rows_forward(state)) == state
		assert mix_columns_backward(mix_columns_forward(state)) == state
		assert aes_decrypt_round(aes_encrypt_round(state)) == state
		
		assert shift_rows_forward(shift_rows_backward(state)) == state
		assert mix_columns_forward(mix_columns_backward(state)) == state
		assert aes_encrypt_round(aes_decrypt_round(state)) == state
	
	key = Vector([Rijndael(_x) for _x in bytes.fromhex('000102030405060708090a0b0c0d0e0f')])
	for n, k in enumerate(key_schedule_128_forward(key)):
		pass
	for n, k in enumerate(key_schedule_128_backward(key)):
		pass
	assert key == Vector([Rijndael(_x) for _x in bytes.fromhex('000102030405060708090a0b0c0d0e0f')])
	
	key = Vector([Rijndael(_x) for _x in bytes.fromhex('00000000000000000000000000000000')])
	in_vec = Vector([Rijndael(_x) for _x in bytes.fromhex('00000101030307070f0f1f1f3f3f7f7f')])
	out_vec = Vector([Rijndael(_x) for _x in bytes.fromhex('c7d12419489e3b6233a2c5a7f4563172')])
	
	assert out_vec == aes_128_encrypt(forward_key=key, data=in_vec)
	assert in_vec == aes_128_decrypt(backward_key=key, data=out_vec)


