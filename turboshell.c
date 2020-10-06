

/********************************/
/********************************/
#pragma pack(16)

#include <stdio.h>
#include <conio.h>
#include <crtdefs.h>
#include <stdlib.h>
#include <stddef.h>
#include <stdarg.h>
#include <unistd.h>
#include <ctype.h>
#include <stdint.h>
#include <string.H>
#include <mem.h>
#include <stdbool.h>
#define FALSE 0
#define TRUE 1

#include <limits.h>
#include <sys/stat.h>
#include <io.h>
#include <direct.h>
#include <fcntl.h>
#include <errno.h>
#include <time.h>
#include <assert.h>
#include <share.h>
#include <process.h>
#include <search.h>
#include <intrin.H>

#define EQ ==
#define NE !=
#define GE >=
#define LE <=
#define GT >
#define LT <
 
#define AND &&
#define OR ||
#define NOT !

#define bitand &
#define bitor |
#define bitxor ^
#define bitnot ~



/* *********** prototype  ************ */

/* ********************* global ***************** */
typedef char byte;
typedef int word;
typedef long dword;

typedef byte *point;
typedef void *vpoint;

#define SCW static const word
#define SCB static const byte

SCW sntnl07=0x7777;
SCW sntnl01=0x1111;

SCB NOK=0;
SCB OK =1;
#define EQ ==
#define NE !=
#define GE >=
#define LE <=
#define GT >
#define LT <
#define AND &&
#define OR ||
#define NOT !

/* ****************  parametros globales ************** */
/* ************ dim ************ */
#define LIN84 84


SCB kolpan=80;
SCB kolsec=76;
SCB LINPAN=25,LIN10=10;
/****************** leter ******************/
SCB LSPACE=' ',LETERN='n';
SCB LETER0='0';
SCB LETER1='1';
SCB LMARKG='-';
SCB LETERA='a';
SCB LETERI='i';
SCB LETERO='o';
SCB LETERP='p';
SCB LETERU='u';
SCB LASTER='*';
/*********** byte ******************/
SCB BYTETAB=0x09;
SCB BYTEESC=0x1B;
SCB BYTEBS =0x08;
SCB BYTE0D =0x0D;
SCB BYTE0A =0x0A;
SCB BYTEFF =0xFF;
/* ******************* lex parser ********************** */

#define MXLTOK6 6

SCB MXLTOK4=4;
SCB ABCD4=4;
SCB ABCD5=5;

#define ABCD6 6
SCB OKSYN=0;
SCB NPMF1=1;
SCB XRWDLEN=1;

SCW sntnl09=0x9999;
/* **** XRWD ************** */
static word DEFXRWD;
static const point Kxrwd="xrwd";

static word lnumpar,selcmd,numfm;

/***************** type ****************/
SCB THIGH   =100;
SCB TALFA   =111;
SCB TNUMBER =112;
SCB TALFANUM=113;
SCB TSEP    =121;
SCB TMARKG  =122;

/* length  ******************************* */
#define MXFSNAME 10
#define MXEXTENS  4

SCB ALNUMMX=8;
SCB TNUMMXL =4;

SCW sntnl08=0x8888;

/* ********************* syntax repository  ***************** */
SCB GROUPDATA= 8;
SCB sdlrqg=0;
SCB sdlrqp=1;
SCB sdlrqm=2;
SCB sdlrp1=3;
SCB sdlrp2=4;
SCB sdlp3opt=5;
SCB sdlxrwd=6;
SCB sdlf1xrwd=7;
SCB sdlf2xrwd=8;
/******************************/
SCB sdllen=9;
#define SDLBIG 12
SCB sdlbig=SDLBIG;

/* *****  account user login ******************** */
#define ANONE 0
#define AROOT 1
#define AUSER 2
#define ASUPE 3

/* ****  session phase **** */
static word alogin,uaccount,nsufail,insecure;

SCB EDTIMER = 20;
SCB LOCKTIMER=10;

static const enum Esespha {LOFF=0,WCMD=1,ECMD=2};
static byte sespha;
static byte *ACCNAM[5]={"NONE","ROOT","USER","SUPE",NULL};

SCB MAXINTRO=2;
SCW sntnl02=0x2222;

/* ******* var global         ************* */
/**********************************************/
static byte sysopmode,cleantty;

/************** db ********************/
#define MXSYN 50
static byte RESUME[MXSYN][LIN84];
static byte PREFIX[MXSYN][SDLBIG];

SCW sntnl0A=0xAAAA;

/**************** tty buffer ***************/
static byte shared[LIN84];
static byte Keybuf[LIN84];
static byte CMDbuf[LIN84];

SCW sntnl03=0x3333;

/* **************** typedef struct ************************ */
typedef struct
	{
	byte smark,used,group,mod,numpar,files;
	byte tp1,tp2,bp1,bp2,p3opt,xrwd,f1xrwd,f2xrwd;
	point pcmd;byte lcmd;
	point pplain;byte lplain;
	} typesyntax;

typedef struct
	{
	byte m;byte u;point p;byte l;byte t;word v;
	} typaram;

/* registry typedef ********************* */
typedef struct
	{
	byte beginb;
	byte used,dow,up,deep;
	word xdir,ndd,lin;
	byte dname[MXFSNAME];
	byte endb;
	} sysdir;

typedef struct
	{
	byte beginb,used,uxrwd;word up,lba;
	byte fname[MXFSNAME];byte fmark;byte exten[MXEXTENS];byte endb;
	} sysfile;

typedef struct
	{
	byte beginb;byte uname[MXFSNAME];byte umark;
	byte wordkey[MXFSNAME];byte endb;
	} sysuser;

/* end registry typedef **************** */

/* *********** variables globales typedef *********** */
SCW sntnl0D=0xDDDD;

static typesyntax  SYNTAXDB[MXSYN];
static typaram param[MXLTOK6];
static byte paran[MXLTOK6][MXFSNAME];

SCW sntnl0E=0xEEEE;

/* REGISTRY   AREA  FS SYNC ********************* */
/* FS handle */

SCW Oopen=O_EXCL  | O_BINARY | O_RDWR;
SCW Smode=S_IFBLK | S_IFREG | S_IREAD | S_IWRITE | S_IEXEC;

SCB Fname[]="VIRTUAL.DSK";

static word regblen,stdisk,stFSYS,FShandle,workdir;
static dword FSlength;

/* ****************** FS registry ********************* */
#define BEGINB 0xFD
#define ENDB   0xFE

#define MXDIR 12
#define MXFILE 12
#define MXUSER 4
#define FXDIR 3
#define FXFILE 1

#define BLOCK 512
#define CLUSTER 8
#define Clusbyt CLUSTER*BLOCK

#define SZATABn 8
#define SZATAB1 4
#define SZAFILE (MXFILE*CLUSTER)

SCW SZAFS= (SZATABn+SZAFILE);
SCW sntnl0F=0xFFFF;

static sysdir   tabdir[MXDIR];
static sysfile  tabfile[MXFILE];
static sysuser  tabuser[MXUSER];

SCW sntnl04=0x4444;
/* ***** end registry *********************** */

SCW sntnl00=0x0000;

/* DISK IO BUFFERS ********************  */

typedef struct
	{
	byte b[Clusbyt];
	} sysbuf;

static byte sblck[BLOCK];
static sysbuf	tabbuf[2];

/* ************************************************************ */
SCW sntnl05=0x5555;

static byte  *MLIST[]=
{"*BOL"
,"*SYN"
,"13nsnoxxx man the man command"
,"13nsnoxxx apropos list commands on topic"
,"12nnnnrxx who show current account"
,"13ninorxx tty set tty mode from seven color options"
,"12nnnnxxx date show date"
,"12nnnnxxx exit terminates sesion"
,"12nnnndxx halt shutdowns computer"
,"22nnnnxxx pwd print working dir"
,"23ndnorxx cd changes current dir"
,"22nnnnrxx ls list all dir entries"
,"23nsnnrxx find find the dir of a name"
,"23nfnnrwx edit edit a file"
,"23nfnnrrx cat display a file"
,"24nffnrwx mv renames a file"
,"23nfnnrdx rm removes a file"
,"23nfnnrwx create create a flat file with random lines"
,"33nfnnrrx more displays page to page"
,"33nfnnrrx head print head lines"
,"34nfsnrrx grep search a text"
,"33nfnnrrx wc counts the lines"
,"34nffnrrw cp copy a file"
,"42nnnnrxx du display dir size"
,"43ndnnrxx mkdir create a new dir"
,"43ndnnrxx rmdir removes one empty dir"
,"42nnnnwxx df summary of disk space"
,"42nnnnrxx su upgrade session to superuser privileges"
,"44nfmnrwx chmod set file protection xrwd"
,"43nsnnrxx chpassw set new password to 4-8 consonant letters "
,"42nnnndxx format format a block device"
,"42nnnndxx mkfs create a new file system"
,"42nnnndxx fsck check file system"
,"44niindxx kernel tool for test kernel"
,"81nnnnxxx groups man on all group of commands"
,"81nnnnxxx basic basic user commands"
,"81nnnnxxx user using commands and files"
,"81nnnnxxx work commands for files"
,"81nnnndxx personal system administration"
,"81nnnnxxx cuts types shortcuts mode xrwd mods -abcd"
,"81nnnnxxx ascii print ascii table"
,"*ESY"
,"01 command verb not found"
,"02 line too long"
,"03 character error"
,"04 too modifier mark"
,"05 modifier required"
,"06 modifier error"
,"07 bad number of parameters"
,"08 command not found"
,"09 parameter too large"
,"10 wrong number of parameters"
,"11 modifier not found"
,"12 text parameter uppercase"
,"13 command not found"
,"14 parameter one type error"
,"15 parameter two type error"
,"16 number too large"
,"17 unknow parameter type"
,"18 parameter too large"
,"19 text parameter  too large"
,"20 number too big"
,"21 parameter one wrong length"
,"22 parameter two wrong length"
,"23 too parameters"
,"24 function modifier must be after command verb"
,"25 number of modifier restricted"
,"26 modifier mark misplaced"
,"27 function modifier not found"
,"28 bad number of function modifier"
,"29 function modifiers syntax error"
,"30 function modifier not found "
,"31 function modifier repeated"
,"32 file protection syntax error"
,"33 cmd need disk formatted service"
,"34 cmd need fs created service"
,"35 cmd need all services started"
,"36 vocal letter in password"
,"37 password too short"
,"*ABR"
,"u user username, picture AAAA"
,"i int integer, picture 9999"
,"f file filename, picture AAAAAAAA"
,"s string alpha-numeric"
,"d dir directory"
,"m mode one letter from string xrwd"
,"v device device"
,"p pid processpid, picture 9999"
,"g modifier function modifier, one to four letters from -abcd"
,"w password password string, picture AAAAAAAA"
,"*MOD"
,"function modifier -abcd"
,"syntax $ cmdverb -abcd parameters"
,"optional one to four letters of string abcd"
,"*RWD"
,"x 0 xrwd locked"
,"r 1 xrwd read only"
,"w 2 xrwd read and write"
,"d 3 xrwd read write delete"
,"*ERU"
,"01 user not found"
,"02 password error"
,"03 file not found"
,"04 directory not found"
,"05 login still disabled"
,"06 command not found"
,"07 file already exist"
,"08 obs job ended by operator"
,"09 directory already exist"
,"10 obs device format error"
,"11 su command disabled"
,"*EIN"
,"01 memory const value corrupted"
,"02 memory value corrupted"
,"03 check sizing area table failed"
,"04 db syntax check failed"
,"05 db syntax numpar check failed"
,"06 db syntax p3 option test failed"
,"07 reached FS directory registry limit"
,"08 system disk unformatted"
,"09 reached FS file registry limit"
,"10 obs format disk failed"
,"11 obs sync wrong rw length"
,"12 obs not enough free space on disk"
,"13 db RESUME length failed"
,"*ELO"
,"01 obsolete cmd on security lock"
,"02 dir not empty"
,"03 dir is the working directory"
,"04 dir is outside"
,"05 obsolete dir locked"
,"06 dir owner locked"
,"07 su password is shared locked"
,"08 command owner restricted"
,"09 user account"
,"10 command restricted to superuser"
,"11 file one is xrwd protected"
,"12 file two is xrwd protected"
,"13 still on super user account"
,"*DON"
,"01 file removed"
,"02 file duplicated"
,"03 file created"
,"04 file renamed"
,"05 file system created"
,"06 directory created"
,"07 directory deleted"
,"08 device formatted"
,"09 password coded and changed"
,"10 password reset to default"
,"11 Custom password using chpassw cmd"
,"*MAN"
,"man            man start page"
,"man command    man on given command verb"
,"man groups     man on all cmd group"
,"man  basic     basic user commands group 01"
,"man  user      using commands and files group 02"
,"man  work      advanced commands for files group 03"
,"man  personal  administration of the system group 04"
,"man cuts       shortcuts, data types and modes"
,"man  ascii     ASCII table"
,"apropos topic  list command on given topic"
,"*PRO"
," U00 Build undefined                    Propietary software"
," Multiprocessor 64 bit                  Certified security "
," Designed for continous operation                          "
," All rights reserved.       Use restricted to license terms"
," ----------------------------------------------------------"
,"*EOL"
,NULL
};

/********************************************************/

static const enum ENUMCMDVERB
{
 MAN=00,APROPOS,WHO,TTY,DATE			,EXIT,HALT,PWD,CD
,LS,FIND,EDIT,CAT    ,MV					,RM,CREATE,MORE,HEAD
,GREP,WC,CP,DU								,MKDIR,RMDIR,DF,SU
,CHMOD,CHPASSW,FORMAT,MKFS		,FSCK,KERNEL,GROUPS,BASIC,USER
,WORK,PERSONAL,TYPES,ASCII		,S1,S2,S3
,S4,S5,S6,S7									,S8,S47,S48,FAROL
};

/* ******************** END OF LIST ********************** */
SCW sntnl06=0x6666;

/* ***************** prototypes ************** */

/* **** begin code C ************* basic lib *************** */
word divide(word a,word b)
{
word c;

if( (a%b) EQ 0)c=a/b; else c=(a/b)+1;

return c;
}

/* ***************** coder enum field ****************** */

word codexrwd(byte lxrwd)
{
word w;

w=0;while(w LE 3 AND Kxrwd[w] NE lxrwd AND Kxrwd[w] NE 0)w++;
if(w GT 3)w=0;

return w;
}

byte decoxrwd(word nxrwd)
{
word u;byte a;

u=nxrwd;if(u GT 3)u=0;
a=Kxrwd[u];return a;
}

/* dow directory owner ****************+ */
point decodow(word dow)
{
word w;point p;

w=dow;if(w GT 3)w=0;
p=ACCNAM[w];
return p;
}

/* ******************** L4 LIST **************** */
word L4ispoint(point x)
{
byte b;

if(x EQ NULL)return NOK;
b=*x;if(b EQ LASTER)return NOK;
if(isascii(b))return OK;
else return NOK;
}

word L4first(point l4)
{
word i,l;point p;

if(*l4 NE LASTER)return 0;
l=strlen(l4);if(l NE 4)return 0;

i=0;p=MLIST[i];
while(p NE NULL)
	{
	if(strcmp(l4,p) EQ 0 )break;
	i++;p=MLIST[i];
	}

if(p EQ NULL)
	{
	i=0;
	printf(" --- EIN L4first not found %s ",l4);
	}

return i;
}

word L4next(word n)
{
word e;point p;

e=n+1;p=MLIST[e];
if(L4ispoint(p) EQ OK)return e;
return 0;
}

word L4number(point l4,word n)
{
word f,e;point p;

f=L4first(l4);if(f EQ 0)return 0;
e=f+n; /* EIN  no verif posible salto area mensajes */
p=MLIST[e];if(L4ispoint(p) EQ OK)return e;
return 0;
}

void L4print(point l4,word n)
{
word m,l;point p;

if(n LE 0)return;
if(*l4 NE LASTER)return;

l=strlen(l4);if(l NE 4)return;

m=L4number(l4,n);

p=MLIST[m];

if(m EQ 0 OR L4ispoint(p) EQ NOK)
	printf(" --EIN  %s %d %d --- \n",l4,n,m);
else printf(" %4s%s \n",l4,p);
}

void	L4list(point l4)
{
word n;point p;

n=L4first(l4);
while(n NE 0)
	{
	n=L4next(n);
	if(n EQ 0)break;
	p=MLIST[n];
	if(L4ispoint(p) NE OK) break;
	printf("%s\n",p);
	}
}

/*   *************** print numbered L4 message **************** */
void printESY(word n)
{
L4print("*ESY",n);
}

void printERU(word n)
{
L4print("*ERU",n);
}

void printELO(word n)
{
L4print("*ELO",n);
}

void printEIN(word n)
{
L4print("*EIN",n);
}

void printDON(word n)
{
L4print("*DON",n);
}

void printproduct(void)
{
L4list("*PRO");
}

void printENO(void)
{
word e;

e=errno;if(e EQ 0)return;
printf(" ENO%02d %s  \n",e,strerror(e));
}

/* ******************* libr date time timer ************************** */

point today(void)
{
time_t *a,b;point c;

a=&b;b=time(a);c=ctime(a);
if(strlen(c) GT kolsec)c[kolsec]=0;
return c;
}

void printtoday(void)
{
printf(" %s \n",today());
}


dword getunixtime(void)
{
dword t;

t=0;t=biostime(0,t);t=t/18;
return t;
}

/* ************* library keyboard ********************** */
word Khit(void)
{
word sc;

sc=bioskey(1);if(sc EQ 0)return 0; else return sc;
}

void Kflush(void)
{
while(bioskey(1) NE 0)bioskey(0);
}

byte Kgetb(void)
{
word w;byte b;

while(bioskey(1) EQ 0)delay(2000);
w=bioskey(0);b=w&0x00FF;
return b;
}

void Kputch(byte b)
{
putch(b);
}
/* **** libr event ********** */

void Wevent(void)
{
word i,n,sc;

i=0;n=100;
while(i LT n)
	{
	sc=Khit();if(sc NE 0)return;
	delay(100);i++;
	}
}

void scheduler(void)
{
word i,n,sc;

i=0;n=10;
while(i LT n)
	{
	sc=Khit();if(sc NE 0)return;
	delay(10);i++;
	}
}

/* *********** libr printers ************************************ */
void newline(void)
{
printf("\n");
}

/******************************
void screensaver(void)
{
word yyy,xx,yy,xxx,cont;

Kflush();
while(Khit() EQ 0)
	{
	cleantty=NOK;
	for(yyy=12;yyy GE 1;yyy--)
		{
		xxx=2*yyy;cont=0;xx=kolpan-2*xxx;yy=LINPAN-2*yyy;
		while(1)
			{
			word x,y,cc,bb,tt;

			x=random(xx)+xxx;y=random(yy)+yyy;
			cc=random(256);bb=random(16);tt=random(16);
			gotoxy(x,y);textbackground(bb);textcolor(tt);lowvideo();Kputch(cc);
			if(Khit() NE 0)break;
			if(cont GT 4*xx*yy)break;
			Wevent();cont++;
			}
			cont=0;
		}
	}
}
*********************************/


/* *********** Libr VIRTUAL DISK. FS FShandle   ************** */
word isHERE(void)
{
word st;
st=access(Fname,0)+access(Fname,2);
if(st EQ 0) return OK; else return NOK;
}

word isOPEN(void)
{
errno=0;tell(FShandle);
if(errno EQ 0) return OK; else return NOK;
}

void fixOPEN(void)
{
if(isOPEN() NE OK)
	{
	FShandle=99;FShandle=open(Fname,Oopen);
	}
}

void fixCLOSE(void)
{
if(isOPEN() EQ OK AND FShandle GE 5)
	{
	close(FShandle);FShandle=99;
	}
}

void fixEXIST(void)
{
fixCLOSE();
if( isHERE() NE OK)
	{
	FShandle=99;FShandle=creat(Fname,Smode);fixCLOSE();
	}
}

/* ******************** Libr FS RW ********** */
void ABSseekblck(word lba)
{
dword y;

if(lba GE SZAFS)return;
y=lba*BLOCK;
lseek(FShandle,y,SEEK_SET);
}

void ABSseekby(dword bp)
{
dword y;
y=bp;lseek(FShandle,y,SEEK_SET);
}

void FSrewind(void)
{
if(isOPEN() EQ OK)ABSseekby(0);
}

/******************* libr file I/O ****************/

word flba(word f)
{
word c;
c=tabfile[f].lba;return c;
}

point fload(word f,word nb)
{
word lba;point q;

if(f GE MXFILE)return NULL;
q=tabbuf[nb].b;if(q EQ NULL)return q;
lba=flba(f);if(lba LT SZATABn OR lba GE SZAFS)return NULL;
ABSseekblck(lba);read(FShandle,q,Clusbyt);return q;
}

point fsave(word f,word nb)
{
word lba;point q;

if(f GE MXFILE)return NULL;
lba=flba(f);if(lba LT SZATABn OR lba GE SZAFS)return NULL;
q=tabbuf[nb].b;if(q EQ NULL)return q;
ABSseekblck(lba);write(FShandle,q,Clusbyt);return q;
}

void fillbuf(word nb,byte b)
{
word n;point p;

n=Clusbyt;p=tabbuf[nb].b;strnset(p,b,n);
}

void cpbuf(word a,word b)
{
vpoint p;vpoint q;

p=tabbuf[a].b;q=tabbuf[b].b;
if(p EQ NULL OR q EQ NULL)return;
movmem(q,p,Clusbyt);
}

SCW sntnl0B=0xBBBB;
SCW sntnl0C=0xCCCC;

/* ************ SEG SEGMENT library ********** */
word CUTWORD(word x,word lim)
{
word r;

r=x;
if(r LE 0)return 0;
if(r GE lim)return lim;
return r;
}

void SEGFILB(point p,word len,byte b)
{
word i;
for(i=0;i LT len;i++)p[i]=b;
p[len]=0;
}

word COUNTCHTAB(point p)
{
word i,len,ee;

ee=0;len=strlen(p);
for(i=0;i LT len;i++)if(p[i] EQ BYTETAB)ee++;
return ee;
}

word CUTSEG(point pp,word LX)
{
size_t rr;word ii;byte bb;

rr=0;if(pp EQ NULL) return 0;
ii=0;bb=pp[ii];
while(bb NE 0 AND ii LT LX)
	{
	ii++;bb=pp[ii];
	}
rr=ii;pp[rr]=0;return rr;
}

void SETFIELD(const word fl,const point dest,const point src)
{
point d;point s;word i,n,m,ufl;

if(dest EQ NULL)return;
if(fl LE 0)return;
if(fl GT kolsec)return;

ufl=fl-1;n=0;s=src;
if(s NE NULL)while(*s++ NE 0 AND n++ LT kolsec);
if(n GE ufl)m=1;else m=fl-n;
d=dest;s=src;
for(i=0;i LT n;i++)*d++=*s++;
for(i=0;i LT m;i++)*d++=0;
}

void SEGCAT(const point dest,const point src,const word nn,const byte T2)
{
point d;point s;word i,secur;

if(dest EQ NULL)return;
secur=strlen(dest);d=dest+strlen(dest);s=src;i=0;
while(s NE NULL AND *s NE 0 AND *s NE T2 AND isascii(*s) )
	{
	*d=*s;d++;s++;i++;
	if(i EQ nn)break;
	secur++;if(secur GT kolsec)break;
	}
for(;i LT nn;i++)*d++=LSPACE;
*d=0;
}

void segprintline(word l,point pp)
{
word i;point p;

p=pp;for(i=0;i LT l;i++)Kputch(*p++);
newline();
}

void segline(word l,point a,point b)
{
point p;word c;

printf(" %4d>",l);
p=a;c=0;
while(p LE b)
	{
	Kputch(*p);
	if(*p EQ BYTEFF)break;
	c++;if(c GT kolsec)break;
	p++;
	}
newline();
}

/* *********** basic crypto library ****************** */

SCB Ktext[]="abcdefghijklmnopqrstuvwxyz0";
SCB Kcode[]="ibhzmdgqjnowxltrafuyvpksec0";

point code(const point a)
{
word i;point r;point s;
/* nunca code vocal  *********** */
r=shared;
for(i=0;a[i] NE 0;i++)
	{
	byte c,t;

	t=a[i];t=t-LETERA;c=Kcode[t];*r++=c;
	}
*r=0;r=shared;s=strrev(r);return s;
}

point decode(const point a)
{
word i;point r;point s;

r=shared;
for(i=0;a[i] NE 0;i++)
	{
	byte c,t;word j;

	c=a[i];
	for(j=0;Kcode[j] NE LETER0;j++)if(Kcode[j] EQ c)break;
	t=Ktext[j];*r++=t;
	}
*r=0;r=shared;s=strrev(r);return s;
}

/* ***********  lexical libr **************** */

word typebyte(byte b)
{
byte bb;

bb=b & 0x7F;
if(isalpha(bb))  return TALFA;
if(isdigit(bb))  return TNUMBER;
if(bb EQ LSPACE) return TSEP;
if(bb EQ LMARKG) return TMARKG;
return bb;
}

word clasbyte(byte bb,word nsyntax)
{
word ns,t;

ns=nsyntax;t=typebyte(bb);
if(ns EQ 0)return t;

if(ns EQ 1)
	if(t GE THIGH)  return OK;
	else return NOK;

if(ns EQ 2)
	if(t EQ TSEP) return TSEP;
	else return TALFANUM;

return NOK;
}

byte tokentype(point cc)
{
byte ii,ll,t0,ee,tt;

ll=CUTSEG(cc,kolsec);if(ll EQ 0) return 0;
t0=typebyte(cc[0]);if(ll EQ 1) return t0;
ee=0;for(ii=0;ii LT ll;ii++)if(typebyte(cc[ii]) NE t0)ee=1;
if(ee EQ 0)return t0;
ee=0;
for(ii=0;ii LT ll;ii++)
	{
	tt=typebyte(cc[ii]);
	if(tt NE TALFA AND tt NE TNUMBER)ee=1;
	}
if(ee EQ 0)return TALFANUM;
return 0;
}

/*  ********** tty edit readline ************** */
void clrscr(void)
{
{

word Kreadline(word LMX,word ECHO)
{
word palb;dword ttt;
word kcod;byte bl;dword qq;

ttt=getunixtime();
Kflush();
strnset(Keybuf,0,kolsec);palb=0;

while(palb LT LMX)
	{
	qq=getunixtime();
	if(qq-ttt GT EDTIMER)
		{
		palb=0;
    clrscr();
    palb=0;cleantty=NOK;
    break;
		}

  if(Khit() NE 0)
		{
		  kcod=bioskey(0);bl=kcod & 0x00FF;
  		if(bl GE 0x80)continue;
	  	if(bl EQ BYTE0D) break;
		  if(bl EQ BYTEESC AND palb GT 0)
			{
			palb=0;printf("<ESC>");break;
			}

			if(bl EQ BYTEBS AND palb GT 0)
			{
			printf("%c",8);palb--;Keybuf[palb]=0;printf("%c%c",32,8);
			}

			if(clasbyte(bl,1))
			{
			Keybuf[palb]=bl;palb++;
			if(ECHO EQ 0)
				{
				bl=LETERA+random(25);Kputch(bl);
				}
				else Kputch(bl);
			}

		}
		else delay(2000);

	}

Keybuf[palb]=0;newline();

return palb;
}


/* ************ libr build syntax db  ***** */

void buildSYNTAXDB(void)
{
word i,n;

for(i=0;i LT MXSYN;i++)
	{
	SYNTAXDB[i].smark=0xAAAA;SYNTAXDB[i].used=NOK;
	}

n=L4first("*SYN");
for(i=0;n NE 0;i++)
	{
	point p;point q;byte bb;word ii,gg;

	n=L4next(n);if(n EQ 0)break;
	p=MLIST[n];q=p;strcpy(shared,q);

	COUNTCHTAB(shared);

/*	l=COUNTCHTAB(shared);if(l GT 0)printERU(); 4  */

	q=p;strcpy(shared,q);q=shared;gg=strlen(p);gg=CUTWORD(gg,kolsec);

	for(ii=0;ii LT gg;ii++)
		{
		bb=*q;if(bb EQ 0)break;
		if(NOT isalnum(bb) )*q=LSPACE;
		q++;
		}
		*q=0;CUTSEG(shared,kolsec);

markused:
	SYNTAXDB[i].used=OK;

groupleter:
	SYNTAXDB[i].group=shared[sdlrqg]-LETER0+0;

numbermods:
	bb=shared[sdlrqm]-LETER0;SYNTAXDB[i].mod=0;
	if(bb GE 0 AND bb LE ABCD4)SYNTAXDB[i].mod=bb;

numpar:
	SYNTAXDB[i].numpar=shared[sdlrqp]-LETER0;
	if(SYNTAXDB[i].numpar GT MXLTOK4)printEIN(5);

tpxybpx:
		{
		byte a,b,c;
/***************************************************/
		a=shared[sdlrp1];b=shared[sdlrp2];

		SYNTAXDB[i].files=0;
		if(a EQ 'f')SYNTAXDB[i].files++;
		if(b EQ 'f')SYNTAXDB[i].files++;

		SYNTAXDB[i].tp1=a;SYNTAXDB[i].tp2=b;

		SYNTAXDB[i].bp1=LETERA;
		if(a EQ LETERI OR a EQ LETERP )SYNTAXDB[i].bp1=LETERI;
		if(a EQ LETERN)SYNTAXDB[i].bp1=a;

		SYNTAXDB[i].bp2=LETERA;
		if(b EQ LETERI OR b EQ LETERP )SYNTAXDB[i].bp2=LETERI;
		if(b EQ LETERN)SYNTAXDB[i].bp2=b;

/****************************************************/
		SYNTAXDB[i].p3opt=0;
		if(SYNTAXDB[i].numpar EQ 3
			AND shared[sdlp3opt] EQ LETERO)SYNTAXDB[i].p3opt=1;

		SYNTAXDB[i].xrwd=shared[sdlxrwd];
		SYNTAXDB[i].f1xrwd=shared[sdlf1xrwd];
		SYNTAXDB[i].f2xrwd=shared[sdlf2xrwd];

		c=LETER1;c++;
		if(a NE LETERN) c++;
		if(b NE LETERN) c++;
		if(SYNTAXDB[i].group NE GROUPDATA AND shared[sdlrqp] NE c)printEIN(4);
		}

comaYxplain:
		{
		q=p;while(isalnum(*q))q++;
		while(NOT isalnum(*q))q++;
		SYNTAXDB[i].pcmd=q;while(isalnum(*q))q++;
		SYNTAXDB[i].lcmd=q-SYNTAXDB[i].pcmd;while(NOT isalnum(*q))q++;
		SYNTAXDB[i].pplain=q;SYNTAXDB[i].lplain=strlen(q);
		}
	}
}

/* ******************  L4 build RESUME db ************ */
point abreviat(byte bb)
{
word n;point p;

n=L4first("*ABR");
while(n NE 0)
	{
	n=L4next(n);if(n EQ 0)break;
	p=MLIST[n];if(bb EQ *p)return (p+2);
	}

return NULL;
}

void buildRESUME(void)
{
word icom,f;point r1;point r2;point p;byte i,n,t1,t2;
byte k[ABCD6];byte j[2];

f=L4first("*SYN");
for(icom=0;f NE 0;icom++)
	{
	f=L4next(f);if(f EQ 0)break;
	n=CUTWORD(SYNTAXDB[icom].mod,ABCD4);
/* code encubierto mal */
	j[0]=LMARKG;if(n EQ 0)j[0]=LSPACE;
	strcpy(k,"abcd");for(i=0;i LE 3;i++)if(i GE n)k[i]=LSPACE;
	j[1]=0;k[4]=0;t1=SYNTAXDB[icom].tp1;t2=SYNTAXDB[icom].tp2;
	r1=abreviat(t1);r2=abreviat(t2);

	shared[0]=0;SEGCAT(shared,SYNTAXDB[icom].pcmd,9,LSPACE);
	SEGCAT(shared,j,1,0);SEGCAT(shared,k,5,0);SEGCAT(shared,r1,7,LSPACE);
	SEGCAT(shared,r2,7,LSPACE);SEGCAT(shared,SYNTAXDB[icom].pplain,70,0);
	SETFIELD(kolsec,RESUME[icom],shared);
	PREFIX[icom][0]=0;p=MLIST[f];strcpy(shared,p);shared[sdllen]=0;
	SETFIELD(sdlbig,PREFIX[icom],shared);
	if( strlen(RESUME[icom]) LT 20 )printEIN(13);
	if( strlen(PREFIX[icom]) LT 4  )printEIN(13);
	}
}

/* ****** numbered phase ************ */
word msyntypes(char cc, byte tt)
{
byte xok;

xok=1;
if(cc EQ LETERA AND
	(tt NE TALFANUM AND tt NE TALFA))xok=0;
if(cc EQ LETERI AND tt NE TNUMBER )xok=0;

return xok;
}

word msynlen(byte tt)
{
if(tt EQ LETERU OR tt EQ LETERP)return 0;
return 1;
}

/* funciones de fase numerada *********** */

word lexicalcmd03(void)
{
word cl,i;

cl=CUTSEG(Keybuf,kolsec);
if(cl NE 0 AND NOT isalpha(Keybuf[0])) return 1;
if(cl GT kolsec) return 2;
numfm=0;
for(i=0;i LT cl;i++)
	{
	byte a;

	a=Keybuf[i];
	if(clasbyte(a,1) EQ 0)return 3;
	if(a EQ LMARKG)numfm++;
	if(numfm GT 1)return 4;
	Keybuf[i]=a;
	}
return 0;
}

word commonparse04(void)
{
const byte tokensep[]=" ";point p;byte ii;

for(ii=0;ii LT MXLTOK6;ii++)
	{
	param[ii].u=NOK;param[ii].p=NULL;param[ii].l=0;
	param[ii].t=NOK;param[ii].v=0;
	paran[ii][0]=0;
	}

	lnumpar=0;p=strtok(CMDbuf,tokensep);
	while(p NE NULL)
	{
	word ll;

	ll=CUTSEG(p,kolsec);param[lnumpar].u=OK;
	param[lnumpar].p=p;param[lnumpar].l=ll;
	lnumpar++;p=strtok(NULL,tokensep);
	}

return OKSYN;
}

void structmove(word d,word s)
{
param[d].u=param[s].u;
param[d].p=param[s].p;
param[d].l=param[s].l;
}

word parsenumpar05(void)
{
word ii,tt;

if(lnumpar EQ 0) return 9;
if(lnumpar GT MXLTOK4)return 7;
if(numfm EQ 0 AND lnumpar EQ MXLTOK4)return 23;

modifcheck:
if(numfm EQ 1 AND lnumpar EQ 1)return 24;
if(numfm EQ 1 AND param[NPMF1].l LE 1)return 27;
if(numfm EQ 1 AND param[NPMF1].l GE ABCD6)return 25;
if(numfm EQ 1 AND param[NPMF1].p[0] NE LMARKG)return 26;

if(numfm EQ 0)
	{
	structmove(3,2);structmove(2,1);
	param[NPMF1].u=NOK;
	param[NPMF1].p=NULL;param[NPMF1].l=0;
	lnumpar++;
	}

nrgtest:
if(numfm EQ 1 AND lnumpar LE 1) return 5;
if(numfm EQ 1 AND lnumpar GE 2)if( *param[NPMF1].p
	NE LMARKG)return 6;
if(numfm EQ 1 AND param[NPMF1].l GE ABCD6)return 6;

argtest:
	for(ii=0;ii LT lnumpar;ii++)
	{
	tt=tokentype(param[ii].p);param[ii].t=tt;
	if(tt EQ 0 AND ii NE NPMF1)return 17;
	if(param[ii].t EQ TALFANUM AND param[ii].l GT ALNUMMX)return 18;
	if(param[ii].t EQ TALFA AND param[ii].l GT ALNUMMX)return 19;
	if(param[ii].t EQ TNUMBER AND param[ii].l GT TNUMMXL)return 20;

	if(param[ii].t EQ TNUMBER)param[ii].v=atoi(param[ii].p);
	}

return OKSYN;
}

word dictsearch06(void)
{
word ii,ff,k;

ff=0;selcmd=0;k=L4first("*SYN");
for(ii=0;k NE 0;ii++)
	{
	k=L4next(k);if(k EQ 0)break;

	if(SYNTAXDB[ii].group NE GROUPDATA
	AND SYNTAXDB[ii].lcmd EQ param[0].l)
		{
		word nn;

		nn=strncmp(param[0].p,SYNTAXDB[ii].pcmd,SYNTAXDB[ii].lcmd);
		if(nn EQ 0){ff++;selcmd=ii;}
		}
	}
ii=0;
testcmdsearch:
	if(ff EQ 0) return 8;
	if(ff GT 1) return 13;

return OKSYN;
}

word funmodparse08(void)
{
point p;word c;byte fm[ABCD6];byte a,i;

if(numfm NE 1) return OKSYN;
if(SYNTAXDB[selcmd].mod EQ 0)return OKSYN;
if(SYNTAXDB[selcmd].mod GE ABCD5)return 29;
if(param[NPMF1].l LT 2)return 29;
c=param[NPMF1].l-1;
if(c EQ 0)return 29;
if(c GT ABCD4)return 29;
if(c GT SYNTAXDB[selcmd].mod)return 29;
p=param[NPMF1].p;p++;a=0;
for(i=0;i LT c;i++)
	{
	byte b,mp,mg;

	mp=LETERA;mg=LETERA+SYNTAXDB[selcmd].mod-1;fm[i]=*p;b=fm[i];p++;
	if(b LT mp OR b GT mg)a=1;
	if(a NE 0)break;
	}
if(a NE 0)return 30;
param[NPMF1].t=TALFA;
if(c GE 2)
	{
	byte i,j;

	for(i=0;i LT c;i++)
		for(j=0;j LT c;j++)
			if(i NE j AND fm[i] EQ fm[j])a=1;
	}
if(a NE 0)return 31;
return OKSYN;
}


word cmdparse07(void)
{
if(SYNTAXDB[selcmd].mod EQ 0 AND numfm NE 0)return 11;
if(numfm EQ 1 AND param[NPMF1].l GT SYNTAXDB[selcmd].mod+1)return 28;
if(NOT(SYNTAXDB[selcmd].numpar EQ 3AND SYNTAXDB[selcmd].p3opt EQ 1
AND lnumpar EQ 2))if(lnumpar NE SYNTAXDB[selcmd].numpar)return 10;

if (lnumpar GE MXLTOK4-1)
if( msyntypes(SYNTAXDB[selcmd].bp1,param[2].t) EQ 0)return 13+1;
if (lnumpar EQ MXLTOK4)
if( msyntypes(SYNTAXDB[selcmd].bp2,param[3].t) EQ 0)return 13+2;
if (lnumpar GE MXLTOK4-1)
if( msynlen(SYNTAXDB[selcmd].tp1) EQ 0)return 20+1;
if (lnumpar EQ MXLTOK4)
if( msynlen(SYNTAXDB[selcmd].tp2) EQ 0)return 20+2;

return OKSYN;
}

word selectedparse09(void)
{
byte b;

if(selcmd EQ CHMOD)
	{
	if(param[3].l NE XRWDLEN)return 22;
	if(param[3].t NE TALFA)return 15;
	b=*param[3].p;param[3].v=codexrwd(b);
	}
return OKSYN;
}

word checkresource10(void)
{
word ii;

for(ii=0;ii LT lnumpar;ii++) strcpy(paran[ii],param[ii].p);
return OKSYN;
}

/********* execute given command ************************************** */
word securQ(void)
{
byte ch;const byte klp='y';

printf("   warning  press key 'y' to confirm :");ch=Kgetb();newline();
if(ch EQ klp) return OK; else return NOK;
}

word execSUk(void)
{
word cl;

printf(" login as superuser \n");
printf(" password: ");
cl=Kreadline(ALNUMMX,0);

if(cl LE 3)return NOK;
if(tokentype(Keybuf) NE TALFA)return NOK;

if(strcmp(decode(tabuser[ 3 ].wordkey),Keybuf) NE 0)return NOK;

return OK;
}

void execSU(void)
{
word st;

if(uaccount EQ ASUPE)
  {
  printELO(13);
  return;
  }

if(nsufail GE MAXINTRO)
	{
	printERU(11);return;
	}

st=execSUk();
if(st EQ OK)
  {	uaccount=ASUPE;nsufail=0;
	}
	else
	{	nsufail++;uaccount=alogin;printERU(2);
	}

}

void execHALT(void)
{
	printf(" sync file system. \n");sysopmode=NOK;
}

void execWHO(void)
{
	printf("\n alogin %02d uaccount %02d \n\n",alogin,uaccount);
}


/* ***************** MAN ******************* */

void helpGROUP(word gsel,word opt)
{
word i;
for(i=0;SYNTAXDB[i].pcmd NE NULL;i++)
	{
	switch(opt)
		{
		case 0:
			if(gsel EQ SYNTAXDB[i].group)printf(" %s \n",RESUME[i]);
			break;
		case 1:
			shared[0]=0;SEGCAT(shared,SYNTAXDB[i].pcmd,SYNTAXDB[i].lcmd+1,LSPACE);
			printf(" %s",shared);
			break;
		default:	break;
		}
	}
if(opt EQ 1)newline();
}

void helpASCII(void)
{
word i;

for(i=0x10;i LE 0xFF;i++)
	{
	if(i LE 0x1F)
		{
		if(i EQ 0x10)printf("     ");
		printf("%1X ",(i-0x10));
		}
		else
		{
		if(i EQ 0x80)newline();
		if(i % 0x10 EQ 0)printf("\n %02X ",i);
		printf(" %c",i);
		}
	}
newline();
}

void helpAPI(void)
{
L4list("*API");
}

void helpSEL(word sel)
{
byte a[SDLBIG];

strcpy(shared,PREFIX[sel]);shared[sdllen]=0;
SETFIELD(sdlbig,a,shared);

printf(" man.%02d  \n",sel);
printf("     %s \n",PREFIX[sel]);
printf("     %s \n",RESUME[sel]);
printf(" number of parameters   : %c \n",a[1]);
printf(" function modifiers     : %c \n",a[2]);
printf(" parameter two type     : %c \n",a[3]);
printf("           two optional : %c \n",a[5]);
printf(" parameter three type   : %c \n",a[4]);
}

word mansearchcmd(void)
{
word ww,n,st;point p;

ww=2;n=L4first("*SYN");p=MLIST[n];
while(p NE NULL)
	{
	if(SYNTAXDB[n].lcmd EQ param[ww].l)
		{
		st=strncmp(param[ww].p,SYNTAXDB[n].pcmd,SYNTAXDB[n].lcmd);
		if(st EQ 0)return n;
		}
	n++;p=MLIST[n];
	}
return 0;
}

void execMAN(void)
{
word sel;

if(param[2].u EQ NOK)
  {
  L4list("*MAN");
  printf("\n Consulte   Unix b sico.  Ed. Editorial. \n\n");
  }
else
	{
	sel=mansearchcmd();
	if(sel EQ 0)printERU(6); else helpSEL(sel);
	if(sel EQ 0 OR SYNTAXDB[sel].group NE GROUPDATA)return;
	switch(sel)
		{
		case TYPES:		L4list("*ABR");L4list("*RWD");L4list("*MOD");break;
		case GROUPS:	helpGROUP(0,1);break;
		case BASIC:		helpGROUP(1,0);break;
		case USER :		helpGROUP(2,0);break;
		case WORK :		helpGROUP(3,0);break;
		case PERSONAL:	helpGROUP(4,0);break;
		case ASCII:		helpASCII();break;
		}
	}
}

void execAPROPOSp2(void)
{
point c,e;word i;

for(i=0;SYNTAXDB[i].pcmd NE NULL;i++)
	{
	if(SYNTAXDB[i].group EQ GROUPDATA)continue;
	c=SYNTAXDB[i].pcmd;e=SYNTAXDB[i].pplain;
	if(strstr(c,param[2].p) NE NULL OR strstr(e,param[2].p) NE NULL
	OR strstr(RESUME[i],param[2].p) NE NULL) printf(" %s \n",RESUME[i]);
	}
}

void execAPROPOS(void)
{
if(param[2].u EQ OK) execAPROPOSp2();else helpGROUP(0,1);

printf("\n Consulte   Unix b sico.  Ed. Editorial. \n\n");
}

/*************************************************/

void diskformat(void)
{
word i,j;

FSrewind();
for(i=0;i LT SZAFS;i++)
	{
	printf(" %d",i);
	for(j=0;j LT BLOCK;j++)sblck[j]=i;
	write(FShandle,sblck,BLOCK);
	}
	newline();
}

/* ******************************* */

void formatEXEC(void)
{

fixCLOSE();fixEXIST();fixOPEN();stdisk=OK;
stFSYS=NOK;diskformat();printDON(8);
}


/**** grupo registry directorys **************/

void Edirdeep(void)
{
word i,j,d;

for(i=FXDIR;i LT MXDIR;i++) tabdir[i].deep=0;

i=0;j=0;d=0;
for(i=0;i LT MXDIR;i++)
	{
	if(tabdir[i].used EQ OK)
		{
		d=0;if(i NE 0)d++;
		j=tabdir[i].up;
		while(j NE 0 AND j LT MXDIR AND d LT MXDIR AND tabdir[j].used EQ OK)
			{
			d++;j=tabdir[j].up;
			}
		tabdir[i].deep=d;
		}
	}
}

void FSseekn(word n)
{
word x;

if(n EQ 0)x=0;else x=SZATAB1;
ABSseekblck(x);
}

/* ************* registry sync to disk ************** */

void FSload(word n)
{
word len;vpoint p;

FSseekn(n);
p= &tabdir  ; len=sizeof(tabdir) ;read(FShandle,p,len);
p= &tabfile ; len=sizeof(tabfile);read(FShandle,p,len);
p= &tabuser ; len=sizeof(tabuser);read(FShandle,p,len);
}

void FSsave(word n)
{
word len;vpoint p;

FSseekn(n);
p= &tabdir;len=sizeof(tabdir);write(FShandle,p,len);
p= &tabfile;len=sizeof(tabfile);write(FShandle,p,len);
p= &tabuser;len=sizeof(tabuser);write(FShandle,p,len);
}

void FSsync(void)
{

Edirdeep();if(stFSYS NE OK)return;
FSsave(0);FSsave(1);FSload(0);
}

void FSoptsync(word icmd)
{

if(SYNTAXDB[icmd].files NE 0)FSsync();
if(icmd EQ MKFS)FSsync();
if(icmd EQ MKDIR OR icmd EQ RMDIR)FSsync();
if(icmd EQ CHPASSW)FSsync();
}

void  FSreset(void)
{
word i,u,c;

/* registry reset ********************* */

for(i=0;i LT MXDIR;i++)
	{
	tabdir[i].beginb=BEGINB;tabdir[i].used=NOK;tabdir[i].dow=ANONE;
	tabdir[i].up=0;tabdir[i].deep=0;SETFIELD(MXFSNAME,tabdir[i].dname,"SLOTFREE");
	tabdir[i].endb=ENDB;
	}

tabdir[0].used=OK;tabdir[0].dow=ANONE;tabdir[0].up=0;tabdir[0].deep=0;
SETFIELD(MXFSNAME,tabdir[0].dname,"DISK");

tabdir[1].used=OK;tabdir[1].dow=AROOT;tabdir[1].up=0;tabdir[1].deep=1;
SETFIELD(MXFSNAME,tabdir[1].dname,"ROOT");

tabdir[2].used=OK;tabdir[2].dow=AUSER;tabdir[2].up=0;tabdir[2].deep=1;
SETFIELD(MXFSNAME,tabdir[2].dname,"USER");

/* ************* tabfile ******************* */
for(i=0;i LT MXFILE;i++)
	{
	tabfile[i].beginb=BEGINB;tabfile[i].fmark=0xFFFF;
	tabfile[i].used=NOK;tabfile[i].up=0;tabfile[i].uxrwd=0;
	SETFIELD(MXFSNAME,tabfile[i].fname,"FREEFILE");
	SETFIELD(MXEXTENS,tabfile[i].exten,"FREE");tabfile[i].endb=ENDB;
	}

tabfile[0].used=OK;tabfile[0].uxrwd=0;tabfile[0].up=0;
SETFIELD(MXFSNAME,tabfile[0].fname,"00000000");

/* *********** tabuser **************** */
for(u=0;u LT MXUSER;u++)
	{
	tabuser[u].beginb=BEGINB;tabuser[u].umark=0xBBBB;
	SETFIELD(MXFSNAME,tabuser[u].wordkey,code("pppp"));
	tabuser[u].endb=ENDB;
	}

/* falta usar ACC NAME */

SETFIELD(MXFSNAME,tabuser[0].uname,"none");
SETFIELD(MXFSNAME,tabuser[1].uname,"root");
SETFIELD(MXFSNAME,tabuser[2].uname,"user");
SETFIELD(MXFSNAME,tabuser[3].uname,"supe");

SETFIELD(MXFSNAME,tabuser[0].wordkey,code("none"));
SETFIELD(MXFSNAME,tabuser[1].wordkey,code("root"));
SETFIELD(MXFSNAME,tabuser[2].wordkey,code("user"));
SETFIELD(MXFSNAME,tabuser[3].wordkey,code("supe"));

/* ************** tabLBA ************ */
c= SZATABn;
for(i=0;i LT MXFILE;i++)
	{
	tabfile[i].lba=c;
	c=c+CLUSTER;
	}
}

void helpSESION(void)
{
printf("\n");
printf("password reset to default \n");
printf("Use tty, chpassw, exit, or halt commands to manage session. \n");
printf("\n");

}


void mkfsEXEC(void)
{
FSreset();Edirdeep();stFSYS=OK;
FSsync();

printDON(5);
helpSESION();
}

/* ************************************** */

void fsckEXEC(void)
{
word xstop;byte b;

/*   begin code critical  */
errno=0;tell(FShandle);if(errno NE 0)return;
FSrewind();
/*   end critical code */

printf(" FSSZA:%dblck BLOCK:%dbyts CLUSTER %dbyts \n",SZAFS,BLOCK,CLUSTER);
printf(" SZATABn:%dblck regblen:%dbyts \n",SZATABn,regblen);
printf(" FS limit: %ddir %dfile %daccount \n",MXDIR,MXFILE,MXUSER);

xstop=0;FSrewind();
while(xstop EQ 0)
	{
	printf(" *? quit rewind entry view \n");printf(" *");
	b=0;b=Kgetb();putch(b);newline();
	switch(b)
		{
		case 'r': FSrewind();break;
		case 'q': xstop=1;break;
		case 'e':
			{
			dword i,c,d;

			if(tell(FShandle)+4 GE regblen)FSrewind();
			b=0;while(b NE BEGINB)read(FShandle,&b,1);
			c=tell(FShandle)-1;b=0;while(b NE ENDB)read(FShandle,&b,1);
			d=tell(FShandle)-1;i=d-c+1;printf(" [%ld - %ld] %2ldbytes \n",c,d,i);

			ABSseekby(c);
			for(i=c;i LE d;i++)
				{
				read(FShandle,&b,1);printf("%02X",b);
				}
			newline();ABSseekby(c);
			for(i=c;i LE d;i++)
				{
				read(FShandle,&b,1);if(isprint(b))printf(" %c",b);else printf("  ");
				}
			newline();ABSseekby(d);
			}
			break;

		case 'v':
			{
			word j,f;byte bb;point p;

			clrscr();
			for(f=0;f LT MXFILE;f++)
				{
				printf(" f%2d(%1d) lba %4d ",f,tabfile[f].used,tabfile[f].lba);
				printf(" %9s   ",tabfile[f].fname);
				p=fload(f,0);
				for(j=0;j LT 8;j++)
					{
						bb=*p++;
						if(isprint(bb))printf("%c",bb);
						else printf("<%X>",bb);
					}
				newline();
				}
			}
			break;

		default:break;
		}
	}
}

/* **********  directory with registry only    ********** */
word localdir(void)
{
word sf,i,len;

sf=0;
for(i=0;i LT MXDIR;i++)
	{
	len=strlen(tabdir[i].dname);
	if(tabdir[i].used EQ OK AND tabdir[i].up EQ workdir AND len EQ param[2].l)
		{
		if(strcmp(tabdir[i].dname,param[2].p) EQ 0)
			{
			sf=i;break;
			}
		}
	}
return sf;
}

word Edirned(word sf)
{
word d,f,ndd,nfd,ned;

ndd=0;
for(d=0;d LT MXDIR;d++)
	{
	if(tabdir[d].used EQ OK AND tabdir[d].up EQ sf)ndd++;
	}

nfd=0;
for(f=0;f LT MXFILE;f++)
	{
	if(tabfile[f].used EQ OK AND tabfile[f].up EQ sf)nfd++;
	}

ned=ndd+nfd;return ned;
}

void Enidir(void)
{
word s,d;

for(d=0;d LT MXDIR;d++)
	if(tabdir[d].used EQ OK)
	{
	s=d;
	while(s NE 0)
		{
		s=tabdir[s].up;tabdir[s].ndd++;
		}
	}
}

void Edirlin(void)
{
word q,newq,d,listado,solved,dirused;

dirused=0;for(d=0;d LT MXDIR;d++)if(tabdir[d].used EQ OK) dirused++;
listado=1;q=0;newq=1;
while(1)
	{
	solved=NOK;
	for(d=0;d LT MXDIR;d++)
		{
		if(tabdir[d].used EQ OK AND tabdir[d].up EQ q AND tabdir[d].lin EQ 0)
			{
			newq=d;tabdir[d].lin=listado++;solved=OK;break;
			}
		}
	if(solved EQ NOK) newq=tabdir[q].up;
	q=newq;if(listado GT dirused)break;
	}
}

/********** cmd registry ************************ */

void regdu(void)
{
word lin,dirused,fileused;

	{
	word d,f,i;

	for(d=0;d LT MXDIR;d++)tabdir[d].lin=0;
	f=0;for(i=0;i LT MXFILE;i++)if(tabfile[i].used EQ OK)f++;
	dirused=0;for(d=0;d LT MXDIR;d++)if(tabdir[d].used EQ OK) dirused++;
	fileused=f;
	}
Edirdeep();Enidir();Edirlin();  /* Edirned(i) */

printf(" dir : #%02d \n",dirused);printf(" file: #%02d \n",fileused);
for(lin=1;lin LE dirused;lin++)
	{
	word d;

	for(d=0;d LT MXDIR;d++)
	if(tabdir[d].used EQ OK AND tabdir[d].lin EQ lin)
		{
		word j;

		j=2*tabdir[d].deep;SEGFILB(shared,j,32);
		if(d EQ workdir)printf("*");else printf(" ");
		printf("dir #%02d %s %s ",d,shared,tabdir[d].dname);
		for(j=0;j LT MXFILE;j++)
			{
			if(tabfile[j].used EQ OK AND tabfile[j].up EQ d)printf(" file #%02d",j);
			}
		newline();
		}
	}
}

void regls(void)
{
word i,d,up,ned,a,b;

d=workdir;up=tabdir[d].up;
ned=Edirned(d);

printf("    workdir dir #%02d %10s (%6s)    Cluster %d blcks \n\n"
,d,tabdir[d].dname,decodow(tabdir[d].dow),CLUSTER);
printf("    (.. up) dir #%02d %10s         \n",up,tabdir[up].dname);

for(d=0;d LT MXDIR;d++)
	{
	if(tabdir[d].used EQ OK AND tabdir[d].up EQ workdir)
		printf("    ..dir #%02d %10s   \n",d,tabdir[d].dname);
	}

for(i=0;i LT MXFILE;i++)
	{
	if(tabfile[i].used EQ OK AND tabfile[i].up EQ workdir)
		{
		a=tabfile[i].lba;b=a+CLUSTER-1;
		printf("    file  #%02d %10s (%c) [%4d -%4d] \n"
		,i,tabfile[i].fname,decoxrwd(tabfile[i].uxrwd),a,b);
		}
	}

if(ned EQ 0) printf("     workdir is <empty> \n");
else         printf("     %03d data structures inside workdir \n",ned);
}

void regpwd(void)
{
word a,b,sf,ned;

sf=workdir;
if(sf GT MXDIR)sf=0;
if(tabdir[sf].used EQ NOK)workdir=0;
ned=Edirned(sf);

a=workdir;tabdir[a].xdir=0;
while(a NE 0)
	{
	b=tabdir[a].up;tabdir[b].xdir=a;a=b;
	}

printf("     ");
a=0;
while(a NE workdir)
	{
	printf("%s.",tabdir[a].dname);
	a=tabdir[a].xdir;
	}
printf("%s\n",tabdir[a].dname);


printf("  *dir %02d %s owner:%s l%d ned%2d\n"
,sf,tabdir[sf].dname,decodow(tabdir[sf].dow),tabdir[sf].deep,ned);

if(ned EQ 0)printf("    empty dir \n");


}

void regcd(void)
{
word sf;

if(param[2].u NE OK)
	{
	workdir=tabdir[workdir].up;regpwd();return;
	}
sf=localdir();
if(sf EQ 0)
	{
	printERU(4);return;
	}

if(alogin NE AROOT AND tabdir[sf].dow NE alogin)
	{
	printELO(6);return;
	}

if(sf EQ workdir OR tabdir[sf].up EQ workdir
			OR sf EQ tabdir[workdir].up)workdir=sf;
else printELO(4);
}

void regmkdir(void)
{
word i,sf;

if(tabdir[workdir].dow NE alogin)
	{
	printELO(6);return;
	}

sf=localdir();
if(sf NE 0)
	{
	printERU(9);return;
	}

sf=0;
for(i=FXDIR;i LT MXDIR;i++)
	if(tabdir[i].used EQ NOK)
	{ sf=i;break;
	}

if(sf EQ 0)
	{ printEIN(7);return;
	}

tabdir[sf].used=OK;tabdir[sf].dow=alogin;tabdir[sf].up=workdir;
SETFIELD(MXFSNAME,tabdir[sf].dname,param[2].p);printDON(6);
}

void regrmdir(void)
{
word sf,ned;

sf=0;sf=localdir();
if(sf EQ 0)
	{printERU(4);return;
	}

if(sf GT 0 AND sf LT FXDIR)
	{printERU(4);return;
	}

ned=Edirned(sf);
if(sf EQ workdir)printELO(3);
if(ned GT 0)printELO(2);
if(tabdir[sf].up NE workdir)printELO(4);
if(sf GE FXDIR AND ned EQ 0 AND sf NE workdir AND tabdir[sf].up EQ workdir)
	{
	tabdir[sf].used=NOK;tabdir[sf].dow=ANONE;tabdir[sf].up=0;
	SETFIELD(MXFSNAME,tabdir[sf].dname,"DIREFREE");printDON(7);
	}
}

/* ******* cmd file with registry only ****************** */
word localfile(point fn)
{
word sf,i,flen,lenfn;

sf=0;lenfn=strlen(fn);
for(i=FXFILE; i LT MXFILE;i++)
	{
	flen=strlen(tabfile[i].fname);
	if(tabfile[i].used EQ OK AND tabfile[i].up EQ workdir
	AND flen EQ lenfn)
		{
		if(strcmp(tabfile[i].fname,fn) EQ 0)
			{ sf=i;break;
			}
		}
	}
return sf;
}

void regdf(void)
{
word i,f,w;dword dw;

f=0;for(i=0;i LT MXFILE;i++)if(tabfile[i].used EQ OK)f++;
w=divide(regblen,BLOCK);dw=FSlength/BLOCK;

printf(" FS REGISTRY  used  blocks %04d \n",w);
printf(" FS           free  blocks %04d \n",SZATABn-w);
printf(" FS           total blocks %04d \n",SZATABn);
printf(" FS FILE blocks used  %4d \n",f);
printf(" FS      blocks free  %4d \n",SZAFILE-f);
printf(" FS      blocks total %4d \n",SZAFILE);
printf(" FS size block       %04ld\n",dw);
}

word createfile(point fn)
{
word i,sf,l;

if(fn EQ NULL)return 0;
l=strlen(fn);if(l EQ 0)return 0;
if(*fn EQ ' ')return 0;

sf=0;
for(i=1;i LT MXFILE;i++)
	if(tabfile[i].used EQ NOK)
		{ sf=i;break;
		}

if(sf EQ 0)
	{ printEIN(9);return 0;
	}

tabfile[sf].used=OK;tabfile[sf].uxrwd=DEFXRWD;tabfile[sf].up=workdir;
SETFIELD(MXFSNAME,tabfile[sf].fname,fn);return sf;
}

void remofile(word sf)
{
tabfile[sf].used=NOK;tabfile[sf].uxrwd=0;tabfile[sf].up=0;
SETFIELD(MXFSNAME,tabfile[sf].fname,"SLOTDELE");
}

void renamefile(word sf,point fn)
{

if(sf LE 0)return;
if(sf GE MXFILE)return;
SETFIELD(MXFSNAME,tabfile[sf].fname,fn);printDON(4);
}

/* ******** cmd with DATA *************** */

int absread(int a,int b,int c,void *e);
int biosdisk(int cmd,int drv,int h,int t,int s,int n,void *buf);

void kernelEXEC(void)
{
word fu,n;

fu=param[2].v;n =param[3].v;
printf(" function=%02d number=%04d \n",fu,n);

switch(fu)
	{
	case 21:
		{
		typedef struct
			{
			byte h,s,c;
			} onehsc;
		typedef struct
			{
			byte isboot; onehsc xfirst;	byte idpart; onehsc xlast;
			dword nfirst;	dword nsize;
			} onepart;
		typedef struct
			{
			byte bincode[446]; onepart p[4]; word mark;
			} THEMBR;

		THEMBR A;int i;
    /* bios 2 leer */
		word dr;word fread;

		fread=2;
    A.mark= 0;
    dr=0x80+n;

    errno=0;
		biosdisk( fread, dr  ,0,0,1	,1,&A);printENO();

		printf(" MBR drive %d \n",n);
		for(i=0;i<4;i++)
			{
				printf(" Partition %1d isboot %2X id %2X first %8lX size %8lX \n"
				,i,A.p[i].isboot,A.p[i].idpart,A.p[i].nfirst,A.p[i].nsize);
			}
			printf(" mark %04X \n", A.mark);
		}
		break;


	case 22:
		{
		int dr,num,lba,i;
		typedef struct
			{
			word salto;
			byte elnop,dato[59];
			word clid;
			byte codigo[512-64-2];
			word mark;
			} BSTRAP;

		BSTRAP B;

		dr=n;
    num=1;
    lba=0;
		/* lba: el primero de la particion es el 0 */
		/* dr:  DOS drive 0:A 1:B 2:C 3:D 4:E 5:F 6:G ... */

		B.mark=0;errno=0;

		absread(dr,num,lba,&B);printENO();

		printf("PARTITION BOOTSTRAP drive: %2d \n",n);
		printf("Area Dato \n");
		for(i=0 ; i < 59 ; i++) printf(" %2X",B.dato[i]);
		newline();
		printf(" Salto %04X NOP %2X CLICLD %2X Mark %04X \n"
		,B.salto,B.elnop,B.clid,B.mark);
		}
		break;

	case 993:	renamefile(n,"TMP");	break;
	case 994:	remofile(n);break;

	default:
         printf(" f:  SHOW PARTITION: 21 dr,  22 dr. \n");
         printf("     REMOVE: 993 994.     \n");
         break;
	}
}

void execRM(word f)
{
fillbuf(0,0xFF);fsave(f,0);printDON(1);
}

void execCREATE(word f)
{
byte b;word i,l;point p;
word linea,columna,longitud;
const byte s[]="ZZZZ ab cd efgh ij klmn 0123456789 op qrst uvwx yz AAAA";

columna=40;longitud=strlen(s);
linea=divide(Clusbyt,columna+8)-4;
p=fload(f,0);
for(l=0;l LT linea;l++)
	{
	for(i=0;i LT columna;i++)
		{
		b=random(longitud);*p++=s[b];
		}
	*p++=BYTE0A;
	}
*p=BYTEFF;
fsave(f,0);printDON(3);
}

void EDIThelp(void)
{
printf(" ? help quit rewind print next save  \n");
}

void execEDIT(word f)
{
word xstop,lin;
point buf,p,q,r;
byte b;

xstop=0;EDIThelp();
buf=fload(f,0);
lin=0;p=buf;q=p;while(*q NE BYTE0A)q++;
while(xstop EQ 0)
	{
	segline(lin,p,q);
	printf("  *");b=Kgetb();putch(b);newline();
	switch(b)
		{
		case 'h':	EDIThelp();break;
		case 'q': xstop=1;break;
		case 's':	fsave(f,0);break;
		case 'r':
			lin=0;p=buf;q=p;while(*q NE BYTE0A)q++;
			break;

		case 'n':
			r=q;r++;
			if(*r EQ BYTEFF)
			{
				lin=0;p=buf;q=p;while(*q NE BYTE0A)q++;
			}
			else
			{
			lin++;q++;p=q;while(*q NE BYTE0A)q++;
			}
			break;

		default:	EDIThelp();break;
		}
	}
}

void execCP(word f1,word f2)
{
	fload(f1,0);fsave(f2,0);printDON(2);
}


void execGREP(word gf)
{
word l,f;
point p;point q;point buf;

		f=gf;l=param[3].l;
		if(tabfile[f].used EQ OK)
		{
			buf=fload(f,0);p=buf;
			while(p NE NULL AND (p-buf) LT Clusbyt)
			{
			q=strstr(p,paran[3]);p=q;
			if(p NE NULL)
				{
				printf(" %d %s> ",f,tabfile[f].fname);
				segprintline(l,p);p=p+l;
				}
			}
		}
}

void execCAT(word go,word gf)
{
byte b,k;
word opt,i,n,m,beol,beof,f1;
point buf1;point p;

n=0;m=0;k=0;
beof=0;
opt=go;f1=gf;
buf1=fload(f1,0);p=buf1;

for(i=0;i LT Clusbyt AND beof EQ 0;i++)
	{
	b=*p++;

	beol=0;if(b EQ BYTEFF)beof=1;
	if(b EQ BYTE0A)
		{n++;beol=1;
		}
	m++;
	switch(opt)
		{
		case 0:
			if(beol EQ 1)newline();else Kputch(b);
			break;

		case 1:
			if(beol EQ 1)newline();else Kputch(b);
			if(beol EQ 1 AND n GE LIN10)beof=1;
			break;

		case 2:
			if(beol EQ 1)newline();else Kputch(b);
			if(beol EQ 1 AND n%4 EQ 0)
			{
			printf(" -- ESC ends -- \n");
			k=Kgetb();
			if(k EQ BYTEESC)beof=1;
			}
			break;

		default: break;
		}
	}
newline();
/* if(kesc NE 0)print(8;   */

if(opt EQ 4)
	printf(" wc  %d lines, %d bytes \n",n,m);

}


word executeSIMPLE(word gc,word gf)
{
word next,simple,f1;

next=NOK;simple=gc;f1=gf;
switch(simple)
	{
	case DATE:	printtoday();break;
  case WHO:   execWHO();break;

	case TTY:

		clrscr();
		printf(" tty CONSOLE SVGA 25x80 high color display \n");
		break;

	case EXIT:
		if(uaccount EQ ASUPE)uaccount=alogin;
		else
		{	uaccount=0;alogin=0;cleantty=NOK;
		}
		break;

	case CHMOD:
		tabfile[f1].uxrwd=param[3].v;
		printf(" chmod file %d>%s  mode %c \n"
			,f1,tabfile[f1].fname,decoxrwd(tabfile[f1].uxrwd));
		break;

	case CHPASSW:
		{
		byte vocal[]="aeiouAEIOU";point p;
		/* defined type password */
		if(param[2].l LT 4)  /* mal pass len min */
			{
			printESY(37);break;
			}

		p=strpbrk(param[2].p,vocal);
		if(p EQ NULL)
			{
				SETFIELD(MXFSNAME,tabuser[uaccount].wordkey,code(param[2].p));
				printDON(9);
			}
			else printESY(36);
		}
		break;

	default: next=OK;
	}
return next;
}


void regfind(void)
{
word d,f;

for(f=FXFILE;f LT MXFILE;f++)
	if(tabfile[f].used EQ OK)
	{
	d=tabfile[f].up;
	if(strstr(tabfile[f].fname,paran[2]) NE NULL)
	printf("  f%d %s d%d %s \n",f,tabfile[f].fname
	,d,tabdir[d].dname);
	}
}

word execICMD(word gc,word f,word g)
{
word icmd,f1,f2;

icmd=gc;f1=f;f2=g;

switch (icmd)
	{
	/* cmd without file ****************** */
	case HALT:			execHALT();break;
	case MAN:				execMAN();break;
	case APROPOS:		execAPROPOS();break;
	case SU:       	execSU();break;

	/* ******* cmd with only registry  **************** */
	case PWD:		regpwd();break;
	case CD:		regcd();break;
	case FIND:	regfind();break;
	case MKDIR: regmkdir();break;
	case RMDIR: regrmdir();break;
	case LS:		regls();break;
	case DU:		regdu();break;
	case DF:		regdf();break;

	/* ************* cmd with DATA ***************** */
	case FSCK:  	fsckEXEC();break;
	case MKFS:		mkfsEXEC();break;
	case FORMAT:	formatEXEC();break;
	case KERNEL:		kernelEXEC();break;

	/* *** cmd for FLAT FILE  *************************** */
	case CAT: 	execCAT(0,f1);break;
	case HEAD:	execCAT(1,f1);break;
	case MORE:	execCAT(2,f1);break;
	case WC:		execCAT(4,f1);break;
	case GREP:	execGREP(f1);break;
	case CP:			execCP(f1,f2);break;
	case RM:			execRM(f1);break;
	case CREATE:	execCREATE(f1);break;
	case EDIT:		execEDIT(f1);break;

	}

return OK;
}

word executeLOGIC(word icmd)
{
word xrwd,elo;

/****  logic of : xrwd alogin  uaccount insecure **** */
elo=0;xrwd=SYNTAXDB[icmd].xrwd;

switch(uaccount)
	{
	case ANONE:	elo=9;break;
	case AROOT:	elo=0;break;
	case AUSER: if(xrwd EQ 'w' OR xrwd EQ 'd')elo=10;break;
	case ASUPE: if(xrwd EQ 'd')elo=8;break;
	}

if(icmd EQ CHPASSW AND uaccount EQ ASUPE)elo=7;

if(elo NE 0)
	{ printELO(elo);return NOK;
	}

if(icmd EQ FORMAT OR icmd EQ MKFS)
	{
		word st;
		st=securQ();if(st NE OK)return NOK;
	}
return OK;
}

word xrwdlogic(word icmd,word f1,word f2)
{
word sf1,sf2,cf1,cf2;

/****** intensidad del cambio solicitado frente al permitido ******/
if(alogin EQ AUSER)
	{
/*********** mal 3 ***********/
	sf1=codexrwd( SYNTAXDB[icmd].f1xrwd );
	if(f1 EQ 0)cf1=  3  ; else cf1=tabfile[f1].uxrwd;
	if(sf1 GT cf1)
		{
		printELO(11);return NOK;
		}
	sf2=codexrwd( SYNTAXDB[icmd].f2xrwd );
	if(f2 EQ 0)cf2=  3  ; else cf2=tabfile[f2].uxrwd;
	if(sf2 GT cf2)
		{
		printELO(12);return NOK;
		}
	}

return OK;
}

word executeCMD(word gc)
{
word f1,f2,next,icmd;

icmd=gc;
f1=0;f2=0;

next=executeLOGIC(icmd);

printf("\n <%02d %01d> \n",icmd,next);
if(next EQ NOK)return 10;

/****** cmd and file ****************/

if(SYNTAXDB[icmd].files GE 1)
	{
	f1=localfile(paran[2+0]);
	if(icmd NE CREATE AND icmd NE EDIT AND f1 EQ 0)
		{
		printERU(3);return 12;
		}
	if(SYNTAXDB[icmd].files GE 2)f2=localfile(paran[2+1]);
	}

/********* logica cambio xrwd *************/
next=xrwdlogic(icmd,f1,f2);if (next NE OK)return 12;

/**************************************************/

	switch(icmd)
	{
		case RM:	remofile(f1);break;
		case EDIT:
		{
			if(f1 EQ 0)
			{
				f1=createfile(paran[2]);
				if(f1 EQ 0)return 13;
				else
				{
				fload(f1,0);fillbuf(0,0xFF);fsave(f1,0);
				}
			}
		}
		break;

		case CREATE:
		{
			if(f1 GT 0)
			{ printERU(7);return 14;
			}
			else
			{ f1=createfile(paran[2]);
				if(f1 EQ 0)return 15;
				fload(f1,0);
				fillbuf(0,0xFF);
				fsave(f1,0);
			}
		}
		break;

		case CP:
		if(f2 GT 0)
		{	printERU(7);return 16;
		}
		f2=createfile(paran[3]);if(f2 EQ 0)return 17;
		break;

		case MV:
		if(f2 GT 0) printERU(7); else renamefile(f1,paran[3]);
		break;

		default:	break;
	}

if(icmd EQ MV)return 22;

next=executeSIMPLE(icmd,f1);
if(next EQ NOK)return 18;

next=execICMD(icmd,f1,f2);
if(next EQ NOK)return 19;

return 21;
}

/* **************  login library ******************** */

word isuser(point x)
{
word u,r;

r=0;
for(u=1;u LE 2;u++)
	if(strcmp(tabuser[u].uname,x) EQ 0)r=u;

return r;
}


word loginstate(void)
{
word u;

u=alogin;
if( (u EQ AROOT) OR (u EQ AUSER) ) return OK;

return NOK;
}

void ttylogin(void)
{
dword inicial;word nloginfail;
word xcounter;

insecure=0;uaccount=0;nloginfail=0;

while(nloginfail LT MAXINTRO)
	{
	word cl;

	printf(" username [i-nscr h-lt] :");
  cl=Kreadline(ALNUMMX,1);
  if(cl EQ 0)continue;

/* puertas de emergencia */
	if(cl EQ 1 AND Keybuf[0] EQ 'h')
		{
		exit(0);
		}

	if(cl EQ 1 AND Keybuf[0] EQ 'i')
		{
		alogin=AROOT;insecure=OK;
    uaccount=alogin;
		}
	else
    {
    alogin=isuser(Keybuf);insecure=0;
    if(loginstate()!=OK) alogin=0;
    if(loginstate()==OK) uaccount=alogin;
    }

	if(loginstate() EQ OK)break;
	printERU(1);nloginfail++;
	}

while(nloginfail LT MAXINTRO && loginstate() EQ OK && insecure NE OK)
	{
	word cl;

	printf(" password (a-brt) :");
  cl=Kreadline(ALNUMMX,0);
  if(cl EQ 0) continue;
  if(cl GE 4 AND cl LE 8)
    if( strcmp(decode(tabuser[alogin].wordkey),Keybuf) EQ 0 )
      {
      nloginfail=0;
      break;
      }
	printERU(2);nloginfail++;
	}

inicial=getunixtime();
while(nloginfail GE MAXINTRO)
	{
	alogin=0;uaccount=0;
  clrscr();
  cleantty=NOK;
	if(getunixtime()-inicial GT LOCKTIMER)
		{
		nloginfail=0;cleantty=NOK;
		}
  else
    {
    printERU(5);
    for(xcounter=0;xcounter< 100;xcounter++) delay(10000);
    cleantty=NOK;
    }

	}

}

/* *****  executive code ********************* */

void sntnlcheck(void)
{
word i,e;

e=0;
if(sntnl00 NE 0x0000)e= 1;
if(sntnl01 NE 0x1111)e= 1;
if(sntnl02 NE 0x2222)e= 2;
if(sntnl03 NE 0x3333)e= 3;
if(sntnl04 NE 0x4444)e= 4;
if(sntnl05 NE 0x5555)e= 5;
if(sntnl06 NE 0x6666)e= 6;
if(sntnl07 NE 0x7777)e= 7;
if(sntnl08 NE 0x8888)e= 8;
if(sntnl09 NE 0x9999)e= 9;
if(sntnl0A NE 0xAAAA)e=10;
if(sntnl0B NE 0xBBBB)e=11;
if(sntnl0C NE 0xCCCC)e=12;
if(sntnl0D NE 0xDDDD)e=13;
if(sntnl0E NE 0xEEEE)e=14;
if(sntnl0F NE 0xFFFF)e=15;
if(e NE 0) printEIN(1);

/***** code for compiler tramp ********/
if(e EQ 0 AND (FAROL+1+e) NE MXSYN)e=FAROL;
if(e NE 0) printEIN(1);

/* mxuser es el minimo */
for(i=0;i LT MXUSER;i++)
	{
	if( tabdir[i].beginb  NE BEGINB)e=21;
	if(tabfile[i].beginb  NE BEGINB)e=22;
	if(tabuser[i].beginb  NE BEGINB)e=23;
	}
if(e NE 0) printEIN(2);
}

void rangeconst(void)
{
word a,b;

a=sizeof(tabdir)+sizeof(tabfile)+sizeof(tabuser);
regblen=a;b=divide(a,BLOCK);
if(1*b GE SZATAB1)printEIN(3);
if(2*b GE SZATABn)printEIN(3);

printf("FS DATA ( regblen %4d         ) \n",regblen);
printf("FS DATA ( 1*b %2d SZATAB1 %2d ) \n",1*b,SZATAB1);
printf("FS DATA ( 2*b %2d SZATABn %2d ) \n",2*b,SZATABn);

}

void rangevars(void)
{
/* *** invariant ***** */
if(workdir GE MXDIR)workdir=0;
if(tabdir[workdir].used NE OK)workdir=0;
if(uaccount EQ 0)alogin=0;

/* *** warning and help ****** */
if(stdisk NE OK) printf("noDisk use format cmd \n");
if(stFSYS NE OK) printf("noFS   use mkfs cmd \n");

sntnlcheck();

/* *** evaluate ************* */
randomize();
FSlength=filelength(FShandle);
}

void printmem(void)
{
word a;dword b,c;

b=farcoreleft();c=coreleft();a=biosmemory();

printf(" biosfree %d Kb  Left %ld b farLeft %ld b \n",a,c,b);
}

#define CMDLENMIN 2


void main(void)
{
/* ******************* init main vars ***************** */
uaccount=0;sysopmode=OK;cleantty=OK;sespha=LOFF;

/* *********** start presentation ************ */
schemacolor(7);clrscr();printproduct();

/* build main db ****** */
buildSYNTAXDB();buildRESUME();

/* **** the disk FS   critical code ********* */
FShandle=99;stdisk=NOK;stFSYS=NOK;

if(isHERE() EQ OK)
	{
	stdisk=OK;fixOPEN();
	if( isOPEN() EQ OK)
		{ FSload(0);stFSYS=OK;
		}
	}
if(stFSYS NE OK)
	{ printEIN(8);FSreset();Edirdeep();
	}

/**********************************************/
rangeconst();

/* ************* main while **************** */
rangevars();
printmem();

while(sysopmode EQ OK)
	{
	word esynt,phase,cmdlen;
	SCB *prompt[]={" none!"," root#"," user$"," supe#",NULL};

	scheduler();
	if(uaccount EQ ANONE)
		{ alogin=ANONE;sespha=LOFF;
		}
	rangevars();
	if(cleantty NE OK)
		{ schemacolor(7);clrscr();printproduct();cleantty=OK;
		}

	esynt=0;phase=1;if(sespha NE ANONE)phase=2;
	switch (phase)
		{
		case 1:
			uaccount=0;alogin=0;insecure=0;
      ttylogin();if(alogin EQ ANONE)break;
			uaccount=alogin;workdir=alogin;if(alogin EQ AROOT)workdir=ANONE;
			DEFXRWD=0;if(alogin EQ AUSER)DEFXRWD=3;
			nsufail=0;phase++;
      printf("\n");

		case 2:
      printf(" (a-brt) ");
			if(insecure EQ OK)printf("i!");
			printf("%s",prompt[uaccount]);sespha=WCMD;

			cmdlen=Kreadline(kolsec,1);
      if(cmdlen EQ 0)break;

      /* letras de emergencia */
    	if(cmdlen EQ 1 AND Keybuf[0] EQ 'a')
  		{
		  uaccount=0;alogin=0;cleantty=NOK;
      break;
  		}
      if(cmdlen < CMDLENMIN);

			strcpy(CMDbuf,Keybuf);CUTSEG(CMDbuf,kolsec);
			cmdlen=strlen(CMDbuf);
			sespha=ECMD;phase++;

		case 3:
			esynt=0;selcmd=0;esynt=lexicalcmd03();if(esynt NE 0)break;
			phase++;esynt=commonparse04();if(esynt NE 0)break;
			phase++;esynt=parsenumpar05();if(esynt NE 0)break;
			phase++;esynt=dictsearch06();if(esynt NE 0)break;
			phase++;esynt=cmdparse07();if(esynt NE 0)break;
			phase++;esynt=funmodparse08();if(esynt NE 0)break;
			phase++;esynt=selectedparse09();if(esynt NE 0)break;
			phase++;esynt=checkresource10();if(esynt NE 0)break;
			phase++;
			{
			word st;

			st=executeCMD(selcmd);
      printf("\n <%02d %03d>\n",selcmd,st);
			/* cmd may require registry sync ****** */
			FSoptsync(selcmd);esynt=0;
			}
			break;
		}
		if(esynt NE 0)printESY(esynt);
	}

FSsync();fixCLOSE();
}

