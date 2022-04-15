from Crypto.Util.number import long_to_bytes, bytes_to_long
import numpy as np
from rich.console import Console
from sage.all import *
from rich.progress import track

import argparse
from config import *
class LowMC():
    def __init__(self, R,A,k=None,pt1=None,ct1=None,pt2=None,ct2=None):
        """
        pt1 and ct1 are the known plaintext/ciphertext pair.
        """
        self.R=R
        self.A=A
        self.k=k
        self.pt1 = pt1
        self.ct1 = ct1
        self.pt2 = pt2
        self.ct2 = ct2
    def Sbox(self,st):
        """
        Sbox function
        """
        if st[0:3]==vector(GF(2),[0,0,0]):
            return st
        a = int(st[0])
        b = int(st[1])
        c = int(st[2])
        X = GF(2).polynomial_ring().gen()
        F = GF(8,name='a',modulus=X**3+X+1)
        res = Integer(F(a*(X**2)+b*X+c).inverse_of_unit().integer_representation()).binary()
        while(len(res)<3):
            res = '0'+res
        st[0] = int(res[0])
        st[1] = int(res[1])
        st[2] = int(res[2])
        return st
    def decrypt(self,key):
        """
        Decryption function
        :param ct: ciphertext, string of binaries. ex: '00000100001111101101000110100010111111011001110100100111010000011011000101001100010100011000100101000000110000000011010111011010'
        :param R: Array of round affine matrices. len(R)==number of rounds...
        :param A: Key update matrix
        :param k: number of rounds
        """
        ct = [int(i) for i in self.ct2]
        ct = vector(GF(2),ct)
        R = [Matrix(GF(2),i) for i in self.R]
        A = Matrix(GF(2),self.A)
        k = vector(GF(2),key)
        for rnd in range(len(R)-1,-1,-1):
            ct = ct-(A**(rnd+1))*k
            ct = R[rnd].inverse() * ct
            ct = self.Sbox(ct)
        ct = list(ct)
        ct = ''.join(str(i) for i in ct)
        ct = int(ct,2)
        return long_to_bytes(ct)
    def encrypt(self,pt,key):
        """
        Encryption function
        :param pt: plaintext, string of bytes. ex: 'granteraerenchym'
        :param R: Array of round affine matrices. len(R)==number of rounds...
        :param A: Key update matrix
        :param k: number of rounds
        """
        pt = ''.join([format(ord(i), '08b') for i in pt])
        pt = vector(GF(2),pt)
        R = [Matrix(GF(2),i) for i in self.R]
        A = Matrix(GF(2),self.A)
        k = vector(GF(2),key)
        st=pt
        for rnd in range(len(R)):
            st = self.Sbox(st)
            st = R[rnd]*st
            st += A**(rnd+1) * k
        ct = list(st)
        ct = [str(i) for i in ct]
        ct = ''.join(ct)
        return ct

    def getMatrixSbox(self,majBit):
        """
        Express the sbox as a 128x128 matrix depending on the majority bit. (Here 129x129 because the last )
        """
        if majBit ==0:
            SboxMat = np.eye(129,dtype=int)
            SboxMat[0][1] = 1
            SboxMat[0][0] = 1

            SboxMat[1][0] = 1
            SboxMat[1][1] = 0

            SboxMat[2][0] = 1
            SboxMat[2][1] = 1
            SboxMat[2][2] = 1 

        if majBit ==1:
            SboxMat = np.eye(129,dtype=int)
            SboxMat[0][0] =0 
            SboxMat[0][1] =1 
            SboxMat[0][2] =1 
            SboxMat[0][-1] =1 

            SboxMat[1][1] =1
            SboxMat[1][0] =1
            SboxMat[1][2] =1 
            SboxMat[1][-1] =1 

            SboxMat[2][-1] =1 
            SboxMat[2][2] =1 
        if majBit ==2:
            SboxMat = np.eye(129,dtype=int)
            SboxMat[0][1] = 0
            SboxMat[0][0] = 1

            SboxMat[1][0] = 1
            SboxMat[1][1] = 1

            SboxMat[2][0] = 1
            SboxMat[2][1] = 1
            SboxMat[2][2] = 1 
        return Matrix(GF(2),SboxMat)
    def base_convert(self,i, b):
            """
            Convert int i in base b
            """
            result = []
            while i > 0:
                    result.insert(0, i % b)
                    i = i // b
            return ''.join(str(i) for i in result)

    def augment(self, mat):
            """
            Augment matrix size by adding a row and column of 0's and a 1 in the [-1][-1] position.
            :param mat: 
            """
            a = np.array(mat)
            b = np.array([np.zeros(len(a),dtype=int)])

            c= np.concatenate((a, b), axis=0)
            res = []
            for i in range(len(c)):
                    res.append(np.append(c[i],0))
            res[-1][-1]=1
            return Matrix(GF(2), res)


    def linearization_attack(self):
        """
        Linearization attack function
        """
        rounds = len(self.R)
        all_maj_bits = []
        for i in range(2**(rounds)):
            all_maj_bits.append(self.base_convert(i,2).zfill(rounds))
        all_maj_bits = [[int(i) for i in j] for j in all_maj_bits]    
        ct = self.ct1+'1'
        pt = ''.join([format(ord(i), '08b') for i in self.pt1])
        st= pt + '1'
        st = vector(GF(2),st)
        ct = vector(GF(2),ct)
        all_cst_v = []
        all_mat_A =[]
        KUM = self.augment(Matrix(GF(2),self.A))
        R = [self.augment(Matrix(GF(2), i)) for i in self.R]
        Sboxs = []

        for box in range(2):
            Sboxs.append(self.getMatrixSbox(box))
        for i in track(all_maj_bits,description="Creating Matrices for all Majority bits.."):
            cst = st
            A= KUM
            for j in range(rounds):
                cst = R[j]*Sboxs[i[j]]*cst
                if j>0:
                    A = Matrix(GF(2),R[j]*Sboxs[i[j]] * A) + Matrix(GF(2),KUM)**(j+1)
            all_cst_v.append(cst-ct)
            all_mat_A.append(A)

        for index, i in enumerate(all_mat_A):
            all_mat_A[index]=Matrix(GF(2),i[0:-1,0:-1])
                                
        for index, i in enumerate(all_cst_v):
            temp = i[:-1]
            all_cst_v[index] = vector(GF(2), temp)
        keys = []
        for i in track(range(len(all_maj_bits)),"Solving Gaussian Elimination for all Matrices A..."):
            try:
                key = all_mat_A[i].solve_right(all_cst_v[i])
                key = ''.join([str(i) for i in key])
                if self.encrypt(self.pt1,key) == self.ct1:
                    keys.append(key)
                    console.print("\n[cyan][+]Key found: {}".format(key))
                    console.print("\n[cyan][+]Decryption: {}".format(self.decrypt(key)))

            except Exception as e:
                pass
                #print(all_maj_bits[i])


        return keys
def parse_args():
    '''
    Parse command line flags.
    '''
    parser = argparse.ArgumentParser()
    parser.add_argument('-e','--encrypt', type=str ,default=None, dest='plaintext', help='Encrypt a plaintext')
    parser.add_argument('-d','--decrypt', type=str ,default=None, dest='ciphertext', help='decrypt a ciphertext')
    parser.add_argument('-k','--key', type=str ,default=None, dest='key', help='key for the decryption of a ciphertext')

    results = parser.parse_args()

    return results


if __name__ == '__main__':
    console = Console()
    args = parse_args()
    if args.plaintext:
        machine = LowMC( Q2a_R, Q2a_A, Q2a_k,pt2=Q2a_pt,ct2=None)
        machine.encrypt()
    if args.ciphertext:
        if args.key:
            machine = LowMC(Q2b_R,Q2b_A, pt1=Q2b_pt1,ct1=Q2b_ct1,ct2=args.ciphertext)
            machine.decrypt(k=args.key)
        else:
            q1 = LowMC(Q2b_R,Q2b_A, pt1=Q2b_pt1,ct1=Q2b_ct1,ct2=Q2b_ct2)
            q1.linearization_attack()

            q2 = LowMC(Q2c_R,Q2c_A, pt1=Q2c_pt1,ct1=Q2c_ct1,ct2=Q2c_ct2)
            q2.linearization_attack()
