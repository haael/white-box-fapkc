#!/usr/bin/python3
#-*- coding:utf-8 -*-


from flask import Flask, request, abort
from pathlib import Path
import json
import rings, polynomial


app = Flask('whitebox_fapkc_demo')


root_dir = Path('demo')


mime_type = {}
mime_type['html'] = [('Content-Type', 'application/xhtml+xml;charset=utf-8')]
mime_type['js'] = [('Content-Type', 'application/javascript;charset=utf-8'), ('Cache-Control', 'only-if-cached, max-age=604800')]
mime_type['py'] = [('Content-Type', 'application/python;charset=utf-8'), ('Cache-Control', 'only-if-cached, max-age=604800')]
mime_type['css'] = [('Content-Type', 'text/css;charset=utf-8'), ('Cache-Control', 'only-if-cached, max-age=604800')]
mime_type['png'] = [('Content-Type', 'image/png'), ('Cache-Control', 'only-if-cached, max-age=604800')]
mime_type['txt'] = [('Content-Type', 'text/plain;charset=utf-8'), ('Cache-Control', 'no-store')]
mime_type['json'] = [('Content-Type', 'application/json;charset=utf-8'), ('Cache-Control', 'no-store')]


def make_error_handler(http_error):
	@app.errorhandler(http_error)
	def error_handler(error):
		return (root_dir / 'error.html').read_text(), http_error, mime_type['html']
	error_handler.__name__ = f'error_{http_error}'
	return error_handler

for http_error in [400, 401, 403, 404, 405, 410, 415, 422]:
	make_error_handler(http_error)


def make_resource_handler(extension):
	def resource_handler(resource):
		try:
			with (root_dir / (resource + '.' + extension)).open('rb') as f:
				return f.read(), mime_type[extension]
		except FileNotFoundError:
			abort(404)
	resource_handler.__name__ = f'resource_{extension}'
	return app.route('/<resource>.' + extension)(resource_handler)


for extension in mime_type.keys():
	make_resource_handler(extension)


@app.route('/')
def index_html():
	try:
		return (root_dir / 'index.html').read_text(), mime_type['html']
	except FileNotFoundError:
		abort(404)


ring_types = {}
ring_types['ModularRing'] = rings.ModularRing, ("size",)
ring_types['BooleanRing'] = rings.BooleanRing, ()
#ring_types['GaloisField'] = rings.GaloisField, ("base", "exponent")
#ring_types['BinaryField'] = rings.BinaryField, ("exponent",)
ring_types['RijndaelField'] = rings.RijndaelField, ()


@app.route('/rings')
def rings():
	return json.dumps(list((_key, _value[1]) for (_key, _value) in ring_types.items())), 200, mime_type['json']


@app.route('/random_polynomial', methods=['POST'])
def random_polynomial():
	try:
		ring_type, args = json.loads(request.form['ring'])
		if len(args) != len(ring_types[ring_type][1]):
			raise ValueError
		base_ring = ring_types[ring_type][0].get_algebra(**dict(zip(ring_types[ring_type][1], [int(_arg) for _arg in args])))
		order = int(json.loads(request.form['order']))
		if not 0 <= order <= 6:
			raise ValueError
		variables = [polynomial.Polynomial.var(_x, base_ring) for _x in json.loads(request.form['variables'])]
	except (KeyError, ValueError) as error:
		print(error)
		abort(404)
	
	p = polynomial.Polynomial.random_nonzero(variables=variables, order=order, base_ring=base_ring).canonical()
	return str(p), 200, mime_type['txt']


if __name__ == '__main__':
	app.run(debug=True)
