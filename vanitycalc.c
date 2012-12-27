// Vanity Address Difficulty Python Module
// Adapted from Vanitygen software

#include <Python.h>
#include "pattern.h"

static PyObject *
vanitycalc_getdiff(PyObject *self, PyObject *args)
{
	vg_context_t *vcp = NULL;
    PyObject *patterns;
    int caseinsensitive;
	int addrtype = 0;
    double diff;

    if (!PyArg_ParseTuple(args, "Oi|i", &patterns, &caseinsensitive, &addrtype))
        return NULL;
        
    vcp = vg_prefix_context_new(addrtype, 128, caseinsensitive);
    diff = vg_context_add_patterns(vcp, patterns);
    vg_context_free(vcp);
    
    return Py_BuildValue("d", diff);
}

static PyMethodDef DiffMethods[] = {
{	"getdiff",  vanitycalc_getdiff, METH_VARARGS,
     "Calculate address difficulty."},
    {NULL, NULL, 0, NULL}        /* Sentinel */
};

PyMODINIT_FUNC
initvanitycalc(void)
{
    (void) Py_InitModule("vanitycalc", DiffMethods);
}


