import { Injectable } from '@angular/core';
import { HttpClient, HttpHeaders } from '@angular/common/http';

@Injectable({
	providedIn: 'root'
})
export class UserServiceService {
	private defaultConfigUrl: string = "https://cors-anywhere.herokuapp.com/https://api.yelp.com/v3/businesses/search?"
	private queryConfigUrl: string = "https://cors-anywhere.herokuapp.com/https://api.yelp.com/v3/businesses/search?"
	private test: string = "https://cors-anywhere.herokuapp.com/https://api.yelp.com/v3/businesses/search?categories=restaurant%2Csteak&location=boston";
	constructor(private http: HttpClient) {
	}

	retrieveRestaurants() {
		const headers = new HttpHeaders().set("Authorization",
			"Bearer AfI6PWEeZpUE5nGtm5leLw1RvHZ1Z3mObg-6_AJFA0K1E8Jtr1Vfs8N4KmjhR2PQYa8gkGz9D5tfaPffoabgSe-s8ecTcQafVL8zhg1s7OPAYyOQcEzaQTO8U6yhW3Yx");
		return this.http.get<JSON>(this.queryConfigUrl, { headers });
	}

	buildSearchQuery(category: string, value: string) {
		this.queryConfigUrl += category + "=" + value + "&";
	}

	buildSearchQueryCategory(categories: string) {
		this.queryConfigUrl += "categories=";
		let splitCategories = categories.split(",");
		for (let i = 0; i < splitCategories.length; i++) {
			if (i + 1 == splitCategories.length) {
				this.queryConfigUrl += splitCategories[i];
			}
			else {
				this.queryConfigUrl += splitCategories[i] + "%2C";
			}
		}
	}

	clearSearchQuery() {
		this.queryConfigUrl = this.defaultConfigUrl;
	}
}
