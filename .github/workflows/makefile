all : install_elan checkout_docgen install_python_dependencies mangle_paths export_lean_symbol_info


install_elan :
	curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none -y
	~/.elan/bin/lean --version

checkout_docgen :
	rm -rf doc-gen
	git clone https://github.com/leanprover-community/doc-gen.git doc-gen

install_python_dependencies :
	python -m pip install --upgrade pip
	pip install -r doc-gen/requirements.txt
	ls doc-gen


mangle_paths :
	sh mangle_paths.sh

export_lean_symbol_info :
	sh export_lean_symbol_info.sh

build_html_docs :
	touch __init__.py
	cp build_html_docs.py doc-gen/
	python3 -m pip install mistletoe
	python3 doc-gen/build_html_docs.py -r .. -w 'https://vaibhavkarve.github.io/igl2020-docs/' -t built-docs
