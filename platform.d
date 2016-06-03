// Written in the D programming language
// Author: Timon Gehr
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import std.traits,std.string,std.conv,std.exception;
import util;

enum Compiler{
	TGD, // TODO: fix
	DigitalMars,
	GNU,
	LDC,
	SDC,
}

enum OS{
	FreeStanding,
	linux,
	FreeBSD,
	OpenBSD,
	NetBSD,
	DragonFlyBSD,
	BSD,
	Solaris,
	AIX,
	Haiku,
	SkyOS,
	SysV3,
	SysV4,
	Hurd,
	Android,
	Cygwin,
	MinGW,
	OSX,
	Win32,
	Win64,
}

enum CRuntime{
	NA,
	Bionic,
	DigitalMars,
	Glibc,
	Microsoft,
}

enum Arch{
	NA,
	X86,
	X86_64,
	ARM,
	AArch64,
	Epiphany,
	PPC,
	PPC64,
	IA64,
	MIPS32,
	MIPS64,
	NVPTX,
	NVPTX64,
	SPARC,
	SPARC64,
	S390,
	SystemZ,
	HPPA,
	HPPA64,
	SH,
	SH64,
	Alpha,
}

size_t wordSize(Arch arch){
	final switch(arch) with(Arch){
		case X86: return 32;
		case X86_64: return 64;
		case ARM: return 32;
		case AArch64: return 64;
		case Epiphany: enforce(0,"TODO");
		case PPC: return 32;
		case PPC64: return 64;
		case IA64: return 64;
		case MIPS32: return 32;
		case MIPS64: return 64;
		case NVPTX: return 32;
		case NVPTX64: return 64;
		case SPARC: return 32;
		case SPARC64: return 64;
		case S390: return 32;
		case SystemZ: return 32;
		case HPPA: return 32;
		case HPPA64: return 64;
		case SH: return 32;
		case SH64: return 64;
		case Alpha: return 32; // TODO: check this
		case NA: assert(0);
	}
}


enum FloatABI{
	NA,
	SoftFloat,
	SoftFP,
	HardFloat
}

bool needFloatABI(Arch arch){
	with(Arch) return util.among(arch,ARM,PPC,PPC64,MIPS32,MIPS64,SPARC,SPARC64,Alpha); // TODO: check this
}

enum MipsABI{
	NA,
	O32,
	N32,
	O64,
	N64,
	EABI,
}

enum Endianness{
	LittleEndian,
	BigEndian,
}

enum BinaryFormat{
	NA,
	ELFv1,
	ELFv2,
}

enum InlineASM{
	NA,
	X86,
	X86_64,
}

immutable reservedVersions={
	string[] r=["unittest","assert","none","all"];
	void add(T)(){
		foreach(x;EnumMembers!T){ auto y=to!string(x); if(y!="NA") r~=to!string(y); }
	}
	add!Compiler;
	add!OS; r~="Posix"; r~="Windows";
	foreach(crt;EnumMembers!CRuntime){
		if(crt==CRuntime.NA) continue;
		r~="CRuntime_"~to!string(crt);
	}
	add!Arch;
	foreach(arch;EnumMembers!Arch){
		if(arch==Arch.PPC64) continue; // PPC
		if(!needFloatABI(arch)) continue;
		string str=arch.to!string;
		with(Arch) if(util.among(arch,MIPS64,SPARC64)) continue;
		with(Arch) if(util.among(arch,MIPS32)) str=str[0..$-2];
		static assert(EnumMembers!FloatABI.length==4); // (might need to change)
		foreach(x;EnumMembers!FloatABI){
			if(x==FloatABI.NA) continue;
			if(x==FloatABI.SoftFP && arch!=Arch.ARM) continue;
			r~=str~"_"~to!string(x); 
		}
	}
	foreach(mabi;EnumMembers!MipsABI){
		if(mabi==MipsABI.NA) continue;
		r~="MIPS_"~to!string(mabi);
	}
	add!Endianness;
	add!BinaryFormat;
	foreach(iasm;EnumMembers!InlineASM){
		if(iasm==InlineASM.NA) continue;
		r~="D_InlineAsm_"~to!string(iasm);
	}
	foreach(m;__traits(allMembers,Platform)){
		static if(is(typeof({auto r=__traits(getMember,Platform(),m); return r;}())==bool)){
			static assert(m.startsWith("D_")||m=="ARM_Thumb"||m=="SPARC_V8Plus");
			static if(!util.among(m,"D_Unittest","D_Assert")) r~=m;
		}
	}
	r~=["darwin","Thumb","S390X"]; // deprecated
	return r;
}();
//pragma(msg, reservedVersions);
import std.algorithm,std.array;
static assert(sort(reservedVersions.map!(x=>x[]).array)==sort(import("reservedversions").split('\n').array));
//pragma(msg,sort(reservedVersions.map!(x=>x[]).array).setDifference(sort(import("predefinedversions").split('\n').array)).array);
//pragma(msg,sort(import("predefinedversions").split('\n').array).setDifference(sort(reservedVersions.map!(x=>x[]).array)).array);

struct Platform{
	enum compiler = Compiler.init;
	auto os = OS.linux;
	auto cruntime=CRuntime.Glibc;
	auto arch = Arch.X86_64;

	bool ARM_Thumb=false;
	bool SPARC_V8Plus=false;

	auto floatABI = FloatABI.NA;
	auto mipsABI = MipsABI.NA;
	auto endianness = Endianness.LittleEndian;
	auto binaryFormat = BinaryFormat.ELFv2; // TODO
	
	bool D_Coverage=false;
	bool D_Ddoc=false;
	bool D_Warnings=false;
	@property D_InlineASM(){
		switch(arch) with(Arch){
			case X86: return InlineASM.X86;
			case X86_64: return InlineASM.X86_64;
			default: return InlineASM.NA;
		}
	}
	bool D_X32=false;
	@property size_t wordSize(){ return .wordSize(arch); }
	@property size_t pointerSize(){
		auto wsiz=wordSize;
		if(D_X32){ assert(wsiz==64); return 32; }
		return wsiz;
	}
	@property bool D_LP64(){ return pointerSize==64; }
	bool D_HardFloat=true;
	@property bool D_SoftFloat(){ return !D_HardFloat; }
	bool D_PIC=false;
	bool D_SIMD=true;
	enum D_Version2=true;
	bool D_NoBoundsChecks=false;
	bool D_ObjectiveC=false;
	bool D_Unittest=false;
	bool D_Assert=true;
	string[] predefinedVersions(){
		string[] r=["all"];
		r~=to!string(compiler);
		r~=to!string(os);
		if(os!=OS.Win32&&os!=OS.Win64) r~="Posix"; // TODO: fix
		else r~="Windows";
		r~=to!string(cruntime);
		r~=to!string(arch);
		if(needFloatABI(arch)){
			assert(floatABI != FloatABI.NA);
			auto str=to!string(arch);
			with(Arch) if(util.among(arch,MIPS32,MIPS64,SPARC64)) str=str[0..$-2];
			r~=str~"_"~to!string(floatABI);
		}else assert(floatABI == FloatABI.NA);
		assert(arch==Arch.ARM||!ARM_Thumb);
		assert(arch==Arch.SPARC||arch==Arch.SPARC64||!SPARC_V8Plus);
		assert(floatABI!=FloatABI.HardFloat||D_HardFloat);
		assert(arch==Arch.MIPS32||arch==Arch.MIPS64||mipsABI==MipsABI.NA);
		if(mipsABI!=MipsABI.NA){
			r~=to!string(mipsABI);
			if(mipsABI!=MipsABI.EABI){
				with(MipsABI) assert(arch==Arch.MIPS32 && util.among(mipsABI,O32,N32)||
									 arch==Arch.MIPS64 && util.among(mipsABI,O64,N64)); // TODO: check this
			}
		}
		r~=to!string(endianness);
		if(binaryFormat!=BinaryFormat.NA) r~=to!string(binaryFormat);
		if(D_InlineASM!=InlineASM.NA) r~="D_InlineASM_"~to!string(D_InlineASM);
		foreach(m;__traits(allMembers,Platform)){
			static if(is(typeof({auto r=__traits(getMember,this,m); return r;}())==bool)){
				if(__traits(getMember,this,m)) if(!util.among(m,"D_Unittest","D_Assert")) r~=m;
			}
		}
		if(D_Unittest) r~="unittest";
		if(D_Assert) r~="assert";
		// deprecated versions:
		if(os==OS.OSX) r~="darwin";
		if(ARM_Thumb) r~="Thumb";
		if(arch==Arch.SystemZ) r~="S390X"; // TODO: check this
		return r;
	}
}
// pragma(msg,Platform().predefinedVersions);
