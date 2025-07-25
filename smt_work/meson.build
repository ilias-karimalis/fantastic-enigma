project('osmosis', ['cpp'], default_options : ['cpp_std=c++2a'])

# Source files
model_src_files = files(
	'src/model.cpp',
)

model_include = include_directories('/opt/cvc5/include')

cvc5_dep = declare_dependency(
	include_directories: include_directories('/opt/cvc5/include'),
	link_args: ['-L/opt/cvc5/lib', '-lcvc5']
)

executable(
	'model',
	sources: model_src_files,
	include_directories: model_include,
	dependencies: [cvc5_dep]
)