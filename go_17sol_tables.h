#pragma once
//================== compare band morphed and source 
extern void G17BuildSort(int * band, int * tsort);
extern int G17ComparedOrderedBand(int * zs0, int * band);
extern int G17ComparedOrdered2Bands(int * zs0, int * band);


struct AUTOMORPH {
	int i416;
	int r[3], c[9], m[9], x;// rows columns map filler
	inline void InitBase(int i16 = 0) {
		i416 = i16;
		for (int i = 0; i < 9; i++)		c[i] = m[i] = i;
		for (int i = 0; i < 3; i++)		r[i] = i;
	}
	void Dump() {
		cout << "perm status i416=" << i416 << endl;
		cout << "rows " << r[0] << r[1] << r[2] << endl;
		cout << "cols " << c[0] << c[1] << c[2]
			<< c[3] << c[4] << c[5] << c[6]
			<< c[7] << c[8] << endl;
		cout << "digs " << m[0] << m[1] << m[2]
			<< m[3] << m[4] << m[5] << m[6]
			<< m[7] << m[8] << endl;
	}
};

// minlex starts and gangsters minlex processing t416
struct BANDMINLEX{// receive a band send back i416 and morphing data
	int diag;//temp for debugging
	int * band0; //0 based band int band0 [27] in the calling program
	int box_morphed[3][9], box_mapped[3][9],map[9];
	int minirows[9], *bbx, *ccx, *rrx, ccx2[3], ccx3[3];


	struct PERM{
		int i416;
		int rows[3], cols[9], map[9];
		//uint16_t i416;
		//uint8_t rows[3], cols[9], map[9];
		inline void InitBase(int i16 = 0 ){
			i416 = i16;
			for (int i = 0; i < 9; i++)		cols[i] = map[i] = i;
			for (int i = 0; i < 3; i++)		rows[i] = i;
		}
		void Dump() {
			cout << "perm status i416=" <<i416<< endl; 
			cout << "rows " << rows[0] << rows[1] << rows[2] << endl;
			cout << "cols " << cols[0] << cols[1] << cols[2] 
				<<cols[3] << cols[4] << cols[5] << cols[6]
				<< cols[7] << cols[8]  << endl;  
			cout << "digs " << map[0] << map[1] << map[2]
				<<map[3] << map[4] << map[5] << map[6]
				<< map[7] << map[8]   << endl;
		}
	}*pout;
	void MorphBox(int imbox, int ibox, int * rx, int * cx);
	inline void PermCols(int * source, int * dest, int * cc){
		// unchecked dest must have same first 2 digits  as source
		cc[2] = 3;//0+1+2 sum of indexes
		for (int i = 0; i < 2; i++){
			register int c = source[i]; // digit 0_8 to find in the second minirox
			for (int j = 0; j < 3; j++)
				if (c == dest[j]){ cc[i] = j; cc[2] -= j;	break; }
		}
	}
	int CheckR3c49(int *istart_iend);
	void SetPout(int iret);
	int Getmin(int * b0,PERM * pout_user,int diag=0);
	int Getmin6();
	int Getmin6_Switch();
	int Getmin7();
	int Getmin7_Switch();
	int GetAutoMorphs(int ei416, PERM * tpout);
};

struct MINLEXUSINGBANDS{
	BANDMINLEX::PERM *tpp,pout[3];
	int * b0 ; // original solution grid
	int bdiagonal[81];
	int  iband[3],i1bx[3],ddiag,ntpp;
	int IsLexMinDiag(int * grid, int  ei416,
		BANDMINLEX::PERM *tpp, int ntpp, int diag = 0);
	int IsLexMinDiagB(int * grid, int  i1b1, int  i1b2, int  i1b3,
		BANDMINLEX::PERM *tpp, int ntpp, int diag = 0);
	int IsLexMinDiagBdet( int  i1, int  i2, int  i3,int diagloc=0);
	int IsLexMinDirect(int * grid, int  i1b1, 	BANDMINLEX::PERM *tpp, int ntpp, int diag = 0);
};

extern int perm_0_8_size3[84][3];
extern int perm_0_8_size4[126][4];
extern int t16_min_clues[416];
extern int t416_to_n6[416];
extern int tn6_to_416[416];
extern int t416n5[416];
extern int t416n6[416];
extern int t16_indua[416];
extern int t16_nua[416];
extern int t16_UAs[11041];
const extern char * t416[416];
extern int tgen_band_cat[24][5];
extern int gangster_pairs_in_box[27][2];

//==================
extern int GetI416_L16(char * ze);
extern BANDMINLEX bandminlex;
extern MINLEXUSINGBANDS minlexusingbands;
extern int MinLexUsingBandsCompB23(int * zcomp, int b23[6][9], int diag);
extern int tgen_band_cat[24][5];
extern AUTOMORPH automorphs[519];
extern  BANDMINLEX::PERM automorphsp[519];

extern char tblnauto[416];
extern uint16_t tblnautostart[416];
// tua64 functions follow
//Banbminlex functions follow