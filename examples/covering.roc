app [main!] {
	pkg: "../src/main.roc",
}

import pkg.S2Cap
import pkg.S2CellId
import pkg.S2Earth
import pkg.S2LatLng
import pkg.S2RegionCoverer

## Covers a disc around a point with S2 cells, which is what a spatial index
## stores: the tokens below are the range keys a database would be queried with.
##
## Usage: covering [<lat> <lng> <radius-km> [max-cells]]
##
## With no arguments it covers 2 km around San Francisco with 12 cells.
main! : List(Str) => Try({}, [Exit(I8)])
main! = |args| {
	match parse(args) {
		Err(message) => {
			echo!("${message}\nusage: covering [<lat> <lng> <radius-km> [max-cells]]\n")
			Err(Exit(2))
		}

		Ok({ lat, lng, radius_km, max_cells }) => {
			center = S2LatLng.from_degrees(lat, lng)
			around = S2Cap.from_center_angle(center.to_point(), S2Earth.from_km(radius_km))
			covering = S2RegionCoverer.default().with_max_cells(max_cells).covering(around)

			echo!("leaf ${S2CellId.from_lat_lng(center).to_token()}\n")
			for id in covering {
				echo!("cell ${id.to_token()} at level ${id.level().to_str()}\n")
			}
			Ok({})
		}
	}
}

Args : { lat : F64, lng : F64, radius_km : F64, max_cells : U64 }

parse : List(Str) -> Try(Args, Str)
parse = |args| {
	match args {
		[] => Ok({ lat: 37.7749, lng: -122.4194, radius_km: 2.0, max_cells: 12 })
		[lat, lng, km] => Ok({ lat: f64_arg(lat)?, lng: f64_arg(lng)?, radius_km: f64_arg(km)?, max_cells: 8 })
		[lat, lng, km, max] => Ok({ lat: f64_arg(lat)?, lng: f64_arg(lng)?, radius_km: f64_arg(km)?, max_cells: u64_arg(max)? })
		_ => Err("expected no arguments, or three or four")
	}
}

f64_arg : Str -> Try(F64, Str)
f64_arg = |text| Ok(F64.from_str(text) ? |_| "${text} is not a number")

u64_arg : Str -> Try(U64, Str)
u64_arg = |text| Ok(U64.from_str(text) ? |_| "${text} is not a whole number")
