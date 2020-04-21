import { BrowserModule } from '@angular/platform-browser';
import { NgModule } from '@angular/core';
import { HttpClient, HttpClientModule } from '@angular/common/http';
import { FormsModule } from '@angular/forms';
import { AppComponent } from './app.component';
import { DAppConfiguratorComponent } from './components/d-app-configurator/d-app-configurator.component';
import { FormEntryHungryComponent } from './components/form-entry-hungry/form-entry-hungry.component';
import { FormEntryLocationComponent } from './components/form-entry-location/form-entry-location.component';
import { FormEntryPriceComponent } from './components/form-entry-price/form-entry-price.component';
import { YelpRestaurantListComponent } from './components/yelp-restaurant-list/yelp-restaurant-list.component';
import { UserServiceService } from './services/user-service/user-service.service';
import { FormEntryCategoriesComponent } from './components/form-entry-categories/form-entry-categories.component';
import { FormEntryTermComponent } from './components/form-entry-term/form-entry-term.component';

@NgModule({
  declarations: [
    AppComponent,
    DAppConfiguratorComponent,
    FormEntryHungryComponent,
    FormEntryLocationComponent,
    FormEntryPriceComponent,
    YelpRestaurantListComponent,
    FormEntryCategoriesComponent,
    FormEntryTermComponent
  ],
  imports: [
    BrowserModule,
    HttpClientModule,
    FormsModule
  ],
  providers: [UserServiceService],
  bootstrap: [AppComponent]
})
export class AppModule { }
