#!/usr/bin/env python3
import print_docs

del print_docs.extra_doc_files[:]

print_docs.copy_yaml_files = lambda p: None
print_docs.library_link_roots['igl2020'] = ('https://github.com/vaibhavkarve/'
                                            'igl2020/blob/$GITHUB_SHA/src/')
print_docs.main()
