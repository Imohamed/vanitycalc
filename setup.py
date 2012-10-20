from distutils.core import setup, Extension

module1 = Extension('vanitycalc',
                    sources = ['vanitycalc.c', 'pattern.c'])

setup (name = 'VanityCalc',
       version = '1.0',
       description = 'Calculates vanity address difficulty',
       ext_modules = [module1])
