import unittest
import numpy as np
from air_bounds import derive, P
from interval_air import check
from virtual_trace import encode, evaluate, prefix_weights, dense_fold


class VirtualTraceTests(unittest.TestCase):
    def test_interval_evaluation_at_boolean_and_nonboolean_points(self):
        col=np.array([0,0,P-1,P-1,7,7,7,0],dtype=np.uint32)
        runs=encode(col)
        for point in [[0,0,0],[1,1,1],[1,0,1],[2,3,P-1]]:
            self.assertEqual(evaluate(runs,prefix_weights(point)),dense_fold(col,point))

    def test_rotated_single_cell_failures_and_selector_boundaries(self):
        data=np.zeros((8,1),dtype=np.uint32);changes=[np.array([0])]
        for rot in [0,1]:
            for selector in [None,'first','last','trans']:
                e=['v',0,rot]
                if selector:e=['*',[selector],e]
                for row in range(8):
                    where=(row-rot)%8
                    enabled=(selector is None or
                             selector=='first' and where==0 or
                             selector=='last' and where==7 or
                             selector=='trans' and where!=7)
                    r=check({'constraints':[e]},data,[],changes,{(row,0):1})
                    self.assertEqual(r['all_local_constraints_zero'],not enabled)
                    if enabled:self.assertEqual(r['failures'][0]['first_bad_row'],where)

    def test_static_bounds_require_no_wrap_and_unconditional_bitness(self):
        x=['v',0,0];y=['v',1,0]
        boolean=['*',x,['+',x,['-',['c',1]]]]
        affine=['+',y,['-',['*',['c',255],x]]]
        bounds,_=derive({'width':2,'constraints':[boolean,affine]})
        self.assertEqual(bounds,[1,255])
        gated=['*',y,boolean]
        bounds,_=derive({'width':2,'constraints':[gated]})
        self.assertEqual(bounds,[P-1,P-1])
        # y = 2*x modulo p does not give a small integer range without x bounds.
        bounds,_=derive({'width':2,'constraints':[['+',y,['-',['*',['c',2],x]]]]})
        self.assertEqual(bounds,[P-1,P-1])


if __name__=='__main__':unittest.main()
