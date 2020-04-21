import React, { PureComponent } from 'react';
import { Link, Route } from 'react-router-dom';

import UsersContainer from './users/UsersContainer';
import UserDetails from './users/UserDetails';

import ServicesContainer from './services/ServicesContainer';
import ServiceDetails from './services/ServiceDetails';

import ServiceCategoriesContainer from './serviceCategories/ServiceCategoriesContainer';
import ServiceCategoryDetails from './serviceCategories/ServiceCategoryDetails';

import FAQs from './faqs/FAQs';
import FAQDetails from './faqs/FAQDetails';

import FAQAnswers from './faas/FAQAnswers';
import FAQAnswerDetails from './faas/FAQAnswerDetails';

import ServiceQuestionsContainer from './serviceQuestions/ServiceQuestionsContainer';
import ServiceQuestionDetails from './serviceQuestions/ServiceQuestionDetails';

import ServiceAnswersContainer from './serviceAnswers/ServiceAnswersContainer';
import ServiceAnswerDetailsContainer from './serviceAnswers/ServiceAnswerDetailsContainer';

export default class Admin extends PureComponent {
  render() {
    return (
      <div>
        <h2>
          <Link to="/admin">Admin</Link>
        </h2>
        <h5>
          <Link to="/">Back to homepage</Link>
        </h5>
        <div>
          <Link to="/admin/users">Users</Link>
          <Route path="/admin/users" exact component={UsersContainer} />
        </div>
        <div>
          <Link to="/admin/users/1">User Details</Link>
          <Route path="/admin/users/:id" exact component={UserDetails} />
        </div>
        <div>
          <Link to="/admin/services">Services</Link>
          <Route path="/admin/services" exact component={ServicesContainer} />
        </div>
        <div>
          <Link to="/admin/services/1">Services Details</Link>
          <Route path="/admin/services/:id" exact component={ServiceDetails} />
        </div>
        <div>
          <Link to="/admin/service-categories">Service Categories</Link>
          <Route
            path="/admin/service-categories"
            exact
            component={ServiceCategoriesContainer}
          />
        </div>
        <div>
          <Link to="/admin/service-categories/1">Service Category Details</Link>
          <Route
            path="/admin/service-categories/:id"
            exact
            component={ServiceCategoryDetails}
          />
        </div>
        <div>
          <Link to="/admin/faqs">Frequently Asked Questions</Link>
          <Route path="/admin/faqs" exact component={FAQs} />
        </div>
        <div>
          <Link to="/admin/faqs/1">Frequently Asked Questions Details</Link>
          <Route path="/admin/faqs/:id" exact component={FAQDetails} />
        </div>
        <div>
          <Link to="/admin/faas">Frequently Asked Question Answers</Link>
          <Route path="/admin/faas" exact component={FAQAnswers} />
        </div>
        <div>
          <Link to="/admin/faas/1">
            Frequently Asked Question Answer Details
          </Link>
          <Route path="/admin/faas/:id" exact component={FAQAnswerDetails} />
        </div>
        <div>
          <Link to="/admin/service-questions">Service Questions</Link>
          <Route
            path="/admin/service-questions"
            exact
            component={ServiceQuestionsContainer}
          />
        </div>
        <div>
          <Link to="/admin/service-questions/1">Service Question Details</Link>
          <Route
            path="/admin/service-questions/:id"
            exact
            component={ServiceQuestionDetails}
          />
        </div>
        <div>
          <Link to="/admin/service-answers">Service Answers</Link>
          <Route
            path="/admin/service-answers"
            exact
            component={ServiceAnswersContainer}
          />
        </div>
        <div>
          <Link to="/admin/service-answers/1">Service Answers Details</Link>
          <Route
            path="/admin/service-answers/:id"
            exact
            component={ServiceAnswerDetailsContainer}
          />
        </div>
      </div>
    );
  }
}
